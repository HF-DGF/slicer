#include "Graphs/SVFG.h"
#include "SVF-LLVM/LLVMUtil.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "Util/Options.h"
#include "WPA/Andersen.h"

#include <fstream>
#include <sstream>

using namespace llvm;
using namespace std;
using namespace SVF;
using namespace LLVMUtil;

// 在计算基本块级别距离时，函数级别距离的倍数
#define CONST_C  10

static llvm::cl::opt<std::string> InputFilename( cl::Positional, llvm::cl::desc( "<input bitcode>" ),
                                                 llvm::cl::init( "-" ) );

static llvm::cl::opt<std::string> TargetsFile( "targets", llvm::cl::desc( "specify targes file" ), llvm::cl::Required );

static llvm::cl::opt<bool> DoInstrument( "instrument", llvm::cl::desc( "do instrument" ), llvm::cl::Optional,
                                         llvm::cl::ValueDisallowed );

/*
 * SVF
 */
SVFModule*                                 svfModule;
SVFIR*                                     pag;
PTACallGraph*                              callgraph;
ICFG*                                      icfg;
SVFG*                                      svfg;
std::map<const SVFValue*, const SVFGNode*> svfvalue_svfgnode;

/*
 * LLVM
 */
llvm::Module* LLVM_M;
LLVMContext*  LLVM_C;

/*
 * CRGF
 */
std::set<const SVFGNode*>   targets_svfg_node;
std::set<const ICFGNode*>   targets_icfg_node;
std::set<const BasicBlock*> targets_llvm_bb;
std::set<const SVFBasicBlock*> targets_svf_bbs;

/*
 * CRGF Slice
 */
std::set<const BasicBlock*> forward_slice_svfg_bbs;
std::set<const BasicBlock*> backward_slice_svfg_bbs;
std::set<const BasicBlock*> from_main_icfg_slice_bbs;

std::map<const BasicBlock*, int32_t> bb_score;    // bb to score
std::map<const BasicBlock*, int32_t> bb_slice;    // bb to slice id,  -1 for exit_bb

// 根据 SVFG 计算出的 BB 前后向距离
std::map<const BasicBlock*, double> bb_distance_backward_svfg;
std::map<const BasicBlock*, double> bb_distance_forward_svfg;

// Call graph 相关的
std::set<const SVFFunction *> func_reach_target;  // func reach target by call graph
std::set<const SVFFunction *> func_from_target_continue;  // func reach target by call graph
std::set<const SVFBasicBlock*> pre_tainted_callsite_bbs; // 调用目标函数或切片函数的 callsite BB


// ICFG 后向切片，是前驱节点，仅用来确定偏差块
std::set<const SVFBasicBlock*> backward_slice_pure_svf_icfg_bbs;


// CFG 相关的
std::set<const SVFBasicBlock*> sliced_icfg_bbs; // iCFG 所有切片基本块
std::map<const SVFFunction*, std::map<const SVFBasicBlock*, int>>      func_entry_2_bb_distance;   // [func] [bb_in_func] = distance, 每一个函数中，每一个 BB 到函数入口的最短距离
std::map<const SVFFunction*, std::map<const SVFBasicBlock*, uint32_t>> dist_func_to_one_target_bb; // [func] [target_svf_bb] = distance
std::map<const SVFBasicBlock*, std::map<const SVFBasicBlock*, uint32_t>>  dist_bb_to_one_target_bb;   // [llvm_bb] [target_svf_bb] = distance

// iCFG 最终距离
std::map<const SVFFunction*, double>    func_distance_icfg;   // [func] = distance
std::map<const SVFBasicBlock*, double>  bb_distance_icfg;     // [svf_bb] = distance_final_result

/* 如果一个基本块只有一个后续基本块
 * 在后向切片中，这个后续基本块也在切片中
 * 在运行的时候，这个后续基本块也会被运行
 * 在统计距离的时候，这个后续基本块也有距离 
 * 因此可以将此基本块不插桩，只需要后续基本块的桩就够了 */
std::set<const SVFBasicBlock*> inst_exclude_bbs_backward_icfg;

// 偏差基本块相关的
std::set<const SVFBasicBlock*> critical_bbs;
std::map<const SVFBasicBlock*, std::set<const SVFBasicBlock*>> critical_exit_bbs_map;
std::map<const SVFBasicBlock*, std::set<const SVFBasicBlock*>> critical_solved_bbs_map;
/* exit slice bb，用来提前终止程序 */
std::set<const SVFBasicBlock*> early_exit_bb;


std::string getDebugInfo( const BasicBlock* bb ) {
    const llvm::Function * fun = bb->getParent();
    string funStr = fun->getName().str();
    for ( auto it = bb->begin(), eit = bb->end(); it != eit; ++it ) {
        const Instruction* inst = &( *it );
        std::string        str  = getSourceLoc( inst );
        if ( str != "{  }" && str.find( "ln: 0  cl: 0" ) == str.npos ) return funStr + ":"+str;
    }
    return funStr + ":{ }";
}

static std::string getFileName(std::string path) {
    std::size_t found = path.find_last_of("/\\");
    if (found != std::string::npos)
        return path.substr(found+1);
    return path;
}

static bool getDebugLocOfInst(const Instruction *I, std::string &Filename, unsigned &Line) {
    if (DILocation *Loc = I->getDebugLoc()) {
        Line = Loc->getLine();
        Filename = Loc->getFilename().str();

        if (Filename.empty()) {
            DILocation *oDILoc = Loc->getInlinedAt();
            if (oDILoc) {
            Line = oDILoc->getLine();
            Filename = oDILoc->getFilename().str();
            }
        }
    }

    if (!Filename.empty()) {
        Filename = getFileName(Filename);
    }

    return !Filename.empty() && Line > 0;
}


static bool getDebugLocOfBB(const BasicBlock* bb, std::string &Filename, unsigned &Line) {
    for ( auto it = bb->begin(), eit = bb->end(); it != eit; ++it ) {
        const Instruction* inst = &( *it );
        if (getDebugLocOfInst(inst, Filename, Line))
            return true;
    }
    return false;
}

// 后向距离
int32_t getBBDistance( const BasicBlock* bb ) {
    if ( bb_distance_backward_svfg.find( bb ) != bb_distance_backward_svfg.end() )
        return bb_distance_backward_svfg[ bb ];
    else
        return -1;
}

// 前向深度
int32_t getBBDepth( const BasicBlock* bb ) {
    if ( bb_distance_forward_svfg.find( bb ) != bb_distance_forward_svfg.end() )
        return int32_t(bb_distance_forward_svfg[ bb ] * 100);
    else
        return -1;
}

// 加载目标块信息
std::vector<const SVFGNode*> loadTargets( std::string filename ) {
    auto LM = LLVMModuleSet::getLLVMModuleSet();

    ifstream inFile( filename );
    if ( !inFile ) {
        std::cerr << "can't open target file!" << std::endl;
        exit( 1 );
    }
    std::cout << "loading targets..." << std::endl;
    std::vector<const SVFGNode*>               result;
    std::vector<std::pair<std::string, u32_t>> targets;
    std::string                                line;
    while ( getline( inFile, line ) ) {
        std::string        func;
        uint32_t           num;
        std::string        comma_string;
        std::istringstream text_stream( line );
        getline( text_stream, func, ':' );
        text_stream >> num;
        targets.push_back( make_pair( func, num ) );
    }

    // itreate all basic block and located target NodeID
    for ( const SVFFunction* fit : *svfModule ) {
        Function* F = const_cast<Function*>( dyn_cast<llvm::Function>( LM->getLLVMValue( fit ) ) );

        std::string file_name = "";
        if ( llvm::DISubprogram* SP = F->getSubprogram() ) {
            if ( SP->describes( F ) ) file_name = ( SP->getFilename() ).str();
        }
        bool flag = false;
        for ( auto target : targets ) {
            auto idx = file_name.find( target.first );
            if ( idx != string::npos ) {
                flag = true;
                break;
            }
        }
        if ( !flag ) continue;

        for ( BasicBlock& BB : *F ) {
            for ( Instruction& I : BB ) {
                uint32_t    line_num = 0;
                std::string str      = getSourceLoc( &I );

                if ( SVFUtil::isa<AllocaInst>( I ) ) {
                    for ( llvm::DbgInfoIntrinsic* DII : FindDbgAddrUses( &I ) ) {
                        if ( llvm::DbgDeclareInst* DDI = SVFUtil::dyn_cast<llvm::DbgDeclareInst>( DII ) ) {
                            llvm::DIVariable* DIVar = SVFUtil::cast<llvm::DIVariable>( DDI->getVariable() );
                            line_num                = DIVar->getLine();
                        }
                    }
                } else if ( MDNode* N = I.getMetadata( "dbg" ) ) {
                    llvm::DILocation* Loc = SVFUtil::cast<llvm::DILocation>( N );
                    line_num              = Loc->getLine();
                }

                // if the line number match the one in targets
                for ( auto target : targets ) {
                    auto idx = file_name.find( target.first );
                    if ( idx != string::npos && ( idx == 0 || file_name[ idx - 1 ] == '/' ) ) {
                        if ( target.second == line_num ) {
                            // 是 target BB
                            targets_llvm_bb.insert(&BB);

                            SVFValue* svfvalue = LLVMModuleSet::getLLVMModuleSet()->getSVFValue( &I );
                            assert( svfvalue != nullptr && "SVFValue Pointer cannot be null!" );

                            SVFInstruction* svfinst = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction( &I );
                            assert( svfinst != nullptr && "SVFInstruction Pointer cannot be null!" );
                            assert( svfvalue == svfinst && "SVFValue != SVFInstruction!" );

                            /* locate ICFG Node */
                            ICFGNode* iNode = icfg->getICFGNode( svfinst );
                            assert( iNode != nullptr && "ICFGNode Pointer cannot be null!" );
                            targets_icfg_node.insert( iNode );
                            targets_svf_bbs.insert(iNode->getBB());

                            /* locate SVFG Node */
                            if ( svfvalue_svfgnode.find( svfvalue ) != svfvalue_svfgnode.end() ) {
                                const SVFGNode* snode = svfvalue_svfgnode[ svfvalue ];

                                targets_svfg_node.insert( snode );
                                result.push_back( snode );

                                // maybe new ICFG Node
                                const ICFGNode* icfgNode = snode->getICFGNode();
                                assert( icfgNode != nullptr && "ICFGNode Pointer cannot be null!" );
                                if ( iNode != icfgNode ) {
                                    targets_icfg_node.insert( icfgNode );
                                }

                                const SVFBasicBlock* svfBB = icfgNode->getBB();
                                assert( svfBB != nullptr && "SVFBasicBlock Pointer cannot be null!" );
                                // std::cout << "Target BB Loc: " << svfBB->getSourceLoc() << std::endl;
                            }

                            break;
                        }
                    }
                }
            }
        }
    }
    inFile.close();

    std::cout << "===================================" << std::endl;
    std::cout << "targets size: " << result.size() << std::endl;
    std::cout << "targets SVFG Node size: " << targets_svfg_node.size() << std::endl;
    std::cout << "targets ICFG Node size: " << targets_icfg_node.size() << std::endl;
    std::cout << "targets LLVM BB size: " << targets_llvm_bb.size() << std::endl;
    std::cout << "===================================" << std::endl;
    return result;
}

/// 前向切片，基于 SVFG
void forwardSlicingSVFG( std::set<const SVFGNode*> target_nodes ) {

    SVFIR* pag = svfg->getPAG();

    FIFOWorkList<const SVFGNode*> worklist;
    std::set<const SVFGNode*>     visited;
    std::set<const SVFGNode*>     visited_all;
    int                           count = 0;

    // svfgNode ->  < distance sum,  count >
    std::map<const SVFGNode*, pair<int, int>> tmp_svfg_distance;

    for ( auto node : target_nodes ) {
        visited.clear();
        visited.insert( node );
        visited_all.insert(node);
        worklist.push( node );
        int level = 0;

        while ( !worklist.empty() ) {
            // 按层级遍历，这里也同时记录 bfs 的第几层作为距离
            int levelSize = worklist.size();
            level++;

            for (int _i = 0; _i < levelSize; _i++) {
                count++;

                const SVFGNode* inode = worklist.pop();
                const SVFValue* svalue = inode->getValue();
                if ( !svalue ) continue;

                const llvm::Value* lvalue = LLVMModuleSet::getLLVMModuleSet()->getLLVMValue( svalue );
                if ( llvm::isa<llvm::Instruction>( lvalue ) ) {
                    const llvm::Instruction* linst = llvm::dyn_cast<llvm::Instruction>( lvalue );
                    const llvm::BasicBlock*  bb    = linst->getParent();
                    // std::cout << "Slice BB Loc: " << getDebugInfo( const_cast<BasicBlock*>( bb ) ) << std::endl;
                    forward_slice_svfg_bbs.insert( bb );
                }

                for ( SVFGNode::const_iterator it = inode->OutEdgeBegin(), eit = inode->OutEdgeEnd(); it != eit; ++it ) {
                    SVFGEdge* edge     = *it;
                    SVFGNode* succNode = edge->getDstNode();

                    // 必须放在这里，因为一个 node 可能后多个边进入，放在这里可以累计所有进入的情况
                    tmp_svfg_distance[succNode].first += level;
                    tmp_svfg_distance[succNode].second ++;

                    if ( visited.find( succNode ) == visited.end() ) {
                        visited.insert( succNode );
                        visited_all.insert(succNode);
                        worklist.push( succNode );
                    }
                }
            }
        }
    }

    std::cout << "slice count: " << count << std::endl
              << "forward_slice_svfg_bbs size: " << forward_slice_svfg_bbs.size() << std::endl;


    // 统计，计算 基本块的距离，取基本块中所有切片指令的最小距离作为bb距离的代表
    for (const SVFGNode * snode: visited_all) {
        const SVFValue* svalue = snode->getValue();
        if ( !svalue ) continue;

        const llvm::Value* lvalue = LLVMModuleSet::getLLVMModuleSet()->getLLVMValue( svalue );
        if ( llvm::isa<llvm::Instruction>( lvalue ) ) {
            const llvm::Instruction* linst = llvm::dyn_cast<llvm::Instruction>( lvalue );
            const llvm::BasicBlock*  bb    = linst->getParent();

            if (tmp_svfg_distance[snode].second == 0) continue;

            // 基本块距离为当前基本块所有inst 的最大距离
            double svfg_dis = (double)tmp_svfg_distance[snode].first / (double)tmp_svfg_distance[snode].second;
            bb_distance_forward_svfg[bb] = max(svfg_dis, bb_distance_forward_svfg[bb]);
        }
    }
}


/// 后向切片，基于 SVFG
void backwardSlicingSVFG( std::set<const SVFGNode*> target_nodes ) {

    SVFIR* pag = svfg->getPAG();

    FIFOWorkList<const SVFGNode*> worklist;
    std::set<const SVFGNode*>     visited;
    std::set<const SVFGNode*>     visited_all;
    int                           count = 0;

    // svfgNode ->  < distance sum,  count >
    std::map<const SVFGNode*, pair<int, int>> tmp_svfg_distance;

    for ( auto node : target_nodes ) {
        visited.clear();
        visited.insert( node );
        visited_all.insert(node);
        worklist.push( node );
        int level = 0;

        while ( !worklist.empty() ) {

            // 按层级遍历，这里也同时记录 bfs 的第几层作为距离
            int levelSize = worklist.size();
            level++;

            for (int _i = 0; _i < levelSize; _i++) {
                count++;

                const SVFGNode* inode = worklist.pop();
                const SVFValue* svalue = inode->getValue();
                if ( !svalue ) continue;

                const llvm::Value* lvalue = LLVMModuleSet::getLLVMModuleSet()->getLLVMValue( svalue );
                if ( llvm::isa<llvm::Instruction>( lvalue ) ) {
                    const llvm::Instruction* linst = llvm::dyn_cast<llvm::Instruction>( lvalue );
                    const llvm::BasicBlock*  bb    = linst->getParent();
                    // std::cout << "Slice BB Loc: " << getDebugInfo( const_cast<BasicBlock*>( bb ) ) << std::endl;
                    backward_slice_svfg_bbs.insert( bb );
                }

                for ( SVFGNode::const_iterator it = inode->InEdgeBegin(), eit = inode->InEdgeEnd(); it != eit; ++it ) {
                    SVFGEdge* edge    = *it;
                    SVFGNode* preNode = edge->getSrcNode();

                    // 必须放在这里，因为一个 node 可能后多个边进入，放在这里可以累计所有进入的情况
                    tmp_svfg_distance[preNode].first += level;
                    tmp_svfg_distance[preNode].second ++;

                    if ( visited.find( preNode ) == visited.end() ) {
                        visited.insert( preNode );
                        visited_all.insert(preNode);
                        worklist.push( preNode );
                    }
                }
            }

        }
    }

    std::cout << "slice count: " << count << std::endl
              << "backward_slice_svfg_bbs size: " << backward_slice_svfg_bbs.size() << std::endl;


    // 统计，计算 基本块的距离，取基本块中所有切片指令的最小距离作为bb距离的代表
    for (const SVFGNode * snode: visited_all) {
        const SVFValue* svalue = snode->getValue();
        if ( !svalue ) continue;

        const llvm::Value* lvalue = LLVMModuleSet::getLLVMModuleSet()->getLLVMValue( svalue );
        if ( llvm::isa<llvm::Instruction>( lvalue ) ) {
            const llvm::Instruction* linst = llvm::dyn_cast<llvm::Instruction>( lvalue );
            const llvm::BasicBlock*  bb    = linst->getParent();
            
            // 基本块距离为当前基本块所有inst 的最小距离
            if (tmp_svfg_distance[snode].second == 0) continue;

            double svfg_dis = (double)tmp_svfg_distance[snode].first / (double)tmp_svfg_distance[snode].second;
            // 因为是取最小值，要避免默认0的情况
            if (bb_distance_backward_svfg[bb] == 0) {
                bb_distance_backward_svfg[bb] = svfg_dis;
            } else {
                bb_distance_backward_svfg[bb] = min(svfg_dis, bb_distance_backward_svfg[bb]);
            }
        }
    }
}



/* 后向根据 iCFG 进行切片 */
void backwardSlicingICFG() {
    std::cout << "backwardSlicingICFG, target nodes count: " << targets_icfg_node.size() << std::endl;

    FIFOWorkList<const ICFGNode*>  worklist;
    std::set<const ICFGNode*>      visited;
    int                            count = 0;
    std::map<const ICFGNode*, int> node_distance;

    for ( auto node : targets_icfg_node ) {
        worklist.push( node );

        while ( !worklist.empty() ) {
            const ICFGNode* iNode = worklist.pop();
            count++;

            auto svfBB = iNode->getBB();
            if ( !svfBB ) continue;

            backward_slice_pure_svf_icfg_bbs.insert(svfBB);


            for ( ICFGNode::const_iterator it = iNode->InEdgeBegin(), eit = iNode->InEdgeEnd(); it != eit; ++it ) {
                ICFGEdge* edge = *it;
                assert( edge != nullptr && "edge Pointer cannot be null!" );
                ICFGNode* preNode = edge->getSrcNode();
                assert( preNode != nullptr && "preNode Pointer cannot be null!" );

                if ( visited.find( preNode ) == visited.end() ) {
                    visited.insert( preNode );
                    worklist.push( preNode );
                }
            }
        }
    }

    std::cout << "slice count: " << count << std::endl
              << "backward_slice_pure_svf_icfg_bbs size: " << backward_slice_pure_svf_icfg_bbs.size() << std::endl;
}



/**
 * 统计可以通过函数调用图到达目标的函数
*/
void calcCallGraphReaching() {
	FIFOWorkList<const SVFFunction*> worklist;
	std::set<const SVFFunction*> visited;

	for (const ICFGNode* target_node : targets_icfg_node) {

        const SVFFunction* now_func = target_node->getFun();
        assert( now_func != nullptr && "target_node->getFun() Pointer cannot be null!" );
        visited.insert(now_func);
		worklist.push(now_func);

		while (!worklist.empty()) {

			const SVFFunction* now_func = worklist.pop();
            
            // ## this func reach target func
            func_reach_target.insert(now_func);

		    FunEntryICFGNode* func_entry_node = icfg->getFunEntryICFGNode(now_func);
            assert( func_entry_node != nullptr && "getFunEntryICFGNode Pointer cannot be null!" );
            
			for (ICFGNode::const_iterator it = func_entry_node->InEdgeBegin(), eit =
					func_entry_node->InEdgeEnd(); it != eit; ++it) {

				ICFGEdge* edge = *it;
				ICFGNode* srcNode = edge->getSrcNode();
				const SVFFunction* caller_func = srcNode->getFun();
                if (caller_func == nullptr) continue;

				if ( visited.find(caller_func) == visited.end() ) {
                    visited.insert(caller_func);
					worklist.push(caller_func);
				}
			}
		}
	}
}

/**
 * 函数级别切片，前向从 target 可以到达的函数切片
*/
void calcCallGraphContinue() {
	FIFOWorkList<const SVFFunction*> worklist;
	std::set<const SVFFunction*> visited;

	for (const ICFGNode* target_node : targets_icfg_node) {

        const SVFFunction* now_func = target_node->getFun();
        assert( now_func != nullptr && "target_node->getFun() Pointer cannot be null!" );
        visited.insert(now_func);
		worklist.push(now_func);

		while (!worklist.empty()) {

			const SVFFunction* now_func = worklist.pop();

            // ## 记录后续可能访问到的函数
            func_from_target_continue.insert(now_func);

            for (const SVFBasicBlock* abb : now_func->getBasicBlockList()) {
                for (const SVFInstruction* ains : abb->getInstructionList()) {
                    
                    const SVFCallInst* call_inst = SVFUtil::dyn_cast<SVFCallInst>(ains);
                    if (call_inst == nullptr) continue;

                    const SVFFunction* callee = call_inst->getCalledFunction();
                    if (callee == nullptr) continue;

                    if ( visited.find(callee) == visited.end() ) {
                        visited.insert(callee);
                        worklist.push(callee);
                    }
                }
            }
		}
	}
}



/**
 * 计算 每个可达函数中 每一个 BB 到函数入口的距离
*/
void calcFuncEntry2SliceBBDistance() {

    for (const SVFFunction* svffun: func_reach_target) {

        std::map<const SVFBasicBlock*, int>     entry_2_bb_distance;
        FIFOWorkList<const SVFBasicBlock*>      worklist;
        std::set<const SVFBasicBlock*>          visited;

        const SVFBasicBlock* entry_bb =  svffun->getEntryBlock();
        worklist.push(entry_bb);
        visited.insert(entry_bb);
        entry_2_bb_distance[entry_bb] = 1;

        while ( !worklist.empty() ) {
            const SVFBasicBlock* now_bb = worklist.pop();
            int new_dist = 1 + entry_2_bb_distance[now_bb];

            for (const SVFBasicBlock* succ_bb : now_bb->getSuccessors()) {
                
                if ( visited.find( succ_bb ) == visited.end() ) {
                    worklist.push( succ_bb );
                    visited.insert( succ_bb );
                    entry_2_bb_distance[succ_bb] = new_dist;
                }
            }
        }

        func_entry_2_bb_distance[svffun] = entry_2_bb_distance;
    }

}


/* slice 预先确定函数内的 callsite 基本块
 * 后续函数内切片根据 污染的 callsite 进行遍历 */
void preSliceCallsiteBBs() {
	FIFOWorkList<const FunEntryICFGNode*> worklist;

	for (const SVFBasicBlock* target_bb : targets_svf_bbs) {
		std::set<const FunEntryICFGNode*> visited;

        const SVFFunction* target_func = target_bb->getFunction();
		FunEntryICFGNode* func_entry_node = icfg->getFunEntryICFGNode(target_func);        
		worklist.push(func_entry_node);
        visited.insert(func_entry_node);

		while (!worklist.empty()) {
			const FunEntryICFGNode* func_entry_node = worklist.pop();
            const SVFFunction* called_func = func_entry_node->getFun();

            std::set<const SVFBasicBlock*> callsites;

			for (ICFGNode::const_iterator it = func_entry_node->InEdgeBegin(), eit = func_entry_node->InEdgeEnd(); it != eit; ++it) {
				ICFGEdge* edge = *it;
				ICFGNode* callNode = edge->getSrcNode();

                const SVFBasicBlock* callBB = callNode->getBB();
                if (callBB == nullptr) continue;

                callsites.insert(callBB);
                pre_tainted_callsite_bbs.insert(callBB);
			}

            for (const SVFBasicBlock* callsite : callsites) {
                // 计算 caller Func 到该 target bb 的距离
				const SVFFunction* caller_func = callsite->getFunction();
                if (caller_func == nullptr) continue;

                FunEntryICFGNode* caller_func_entry_node = icfg->getFunEntryICFGNode(caller_func);
                if (visited.find(caller_func_entry_node) == visited.end()) {
                    worklist.push(caller_func_entry_node);
                    visited.insert(caller_func_entry_node);
                }
			}
		}
	}

    pre_tainted_callsite_bbs.insert(targets_svf_bbs.begin(), targets_svf_bbs.end());
}


/**
 * calcCallGraphDistance 利用 call graph 函数调用图 计算函数距离
 * 
 * 给定目标 ICFG 节点，确定目标块，从而获取目标函数 (以函数入口块 代表 函数)
*/
void calcCallGraphDistance() {
	FIFOWorkList<const FunEntryICFGNode*> worklist;
    std::map<const SVFBasicBlock*, std::vector<const SVFFunction*>> bb_call_func;

	// calculate the function distance to each target.
	for (const SVFBasicBlock* target_bb : targets_svf_bbs) {
        const SVFFunction* target_func = target_bb->getFunction();
        assert( target_func != nullptr && "target_bb->getFunction(): Pointer cannot be null!" );
#ifdef CRGF_CG_DISTANCE
        dist_func_to_one_target_bb[target_func][target_bb] = func_entry_2_bb_distance[target_func][target_bb];
#else
        dist_func_to_one_target_bb[target_func][target_bb] = 1;
#endif

		FunEntryICFGNode* func_entry_node = icfg->getFunEntryICFGNode(target_func);
        assert( func_entry_node != nullptr && "icfg->getFunEntryICFGNode(target_func): Pointer cannot be null!" );
        
		worklist.push(func_entry_node);

		while (!worklist.empty()) {
			const FunEntryICFGNode* func_entry_node = worklist.pop();
            const SVFFunction* called_func = func_entry_node->getFun();
            assert( called_func != nullptr && "func_entry_node->getFun(): Pointer cannot be null!" );

            uint32_t called_func_dist = dist_func_to_one_target_bb[called_func][target_bb];

            std::set<const SVFBasicBlock*> callsites;

			for (ICFGNode::const_iterator it = func_entry_node->InEdgeBegin(), eit = func_entry_node->InEdgeEnd(); it != eit; ++it) {
				ICFGEdge* edge = *it;
				ICFGNode* callNode = edge->getSrcNode();

                const SVFBasicBlock* callBB = callNode->getBB();
                if (callBB == nullptr) continue;
                callsites.insert(callBB);
			}

            for (const SVFBasicBlock* callsite : callsites) {
                // 计算 caller Func 到该 target bb 的距离
				const SVFFunction* caller_func = callsite->getFunction();
                if (caller_func == nullptr) continue;

#ifdef CRGF_CG_DISTANCE
                uint32_t caller_dist = func_entry_2_bb_distance[caller_func][callsite];
                if (caller_dist == 0) caller_dist = 1;
#else
                uint32_t caller_dist = 1;
#endif

                // 注意。这里无需 visited 记录进行去重，正是因为这个 if 判断
				if ( dist_func_to_one_target_bb[caller_func].count(target_bb) == 0 ||
                     dist_func_to_one_target_bb[caller_func][target_bb] > caller_dist + called_func_dist ) {
                    
                    // 更新 该函数 到 目标函数 的距离
					dist_func_to_one_target_bb[caller_func][target_bb] = caller_dist + called_func_dist;

				    FunEntryICFGNode* caller_func_entry_node = icfg->getFunEntryICFGNode(caller_func);
                    assert( caller_func_entry_node != nullptr && "icfg->getFunEntryICFGNode(caller_func): Pointer cannot be null!" );
					worklist.push(caller_func_entry_node);
				}

#ifdef CRGF_CG_DISTANCE
                // 计算 callsite BB 到每个 target_bb 的距离
                if (dist_bb_to_one_target_bb[callsite].find(target_bb) == dist_bb_to_one_target_bb[callsite].end()
                    || dist_bb_to_one_target_bb[callsite][target_bb] > 1 + called_func_dist) {

                    dist_bb_to_one_target_bb[callsite][target_bb] = 1 + called_func_dist;
                }
#endif
			}
		}
	}

#ifdef CRGF_CG_DISTANCE
    for (const SVFBasicBlock* target_bb : targets_svf_bbs) {
        dist_bb_to_one_target_bb[target_bb][target_bb] = 0;
    }
#endif

    // 计算函数距离，calculate the harmonic distance to all targets
    for ( auto func : dist_func_to_one_target_bb ) {
        double dis = 0;
        for (auto t : func.second) {
            dis += (double)1 / t.second;
        }
        if (dis > 0) {
            dis = (double)1 / dis;
            func_distance_icfg[func.first] = dis;
        }
    }


#ifndef CRGF_CG_DISTANCE
    // 对于 AFLGo 类型的基本块距离，需要在计算了 func_distance_icfg 后才能计算
    for (const SVFBasicBlock* callsite : pre_tainted_callsite_bbs) {
        // 其他基本块，距离为 1 + C * min(dist_called_func)
        double dis = INT32_MAX;
        for (const SVFFunction* called_func : bb_call_func[callsite]) {
            dis = std::min(dis, 1 + CONST_C * func_distance_icfg[called_func]);
        }
        bb_distance_icfg[callsite] = dis;
    }

    // 目标基本块距离为 0
    for (const SVFBasicBlock* target_bb : targets_svf_bbs) {
        bb_distance_icfg[target_bb] = 0;
    }
#endif
}


#ifdef CRGF_CG_DISTANCE
/**
 * calcCFGDistance 基于每个函数的 CFG 控制流图 计算 BB 到 target 的距离
*/
void calcCFGDistance() {
    std::cout << "pretainted_bbs: " << pre_tainted_callsite_bbs.size() << std::endl;

    // 污染其他没有直接调用 slice func 的基本块
	for (const SVFBasicBlock* bb : pre_tainted_callsite_bbs) {

		FIFOWorkList<const SVFBasicBlock*> worklist;
		worklist.push(bb);
        sliced_icfg_bbs.insert(bb);

		while (!worklist.empty())
		{
			const SVFBasicBlock* vbb = worklist.pop();

			for (const SVFBasicBlock* srcbb : vbb->getPredecessors()) {
                sliced_icfg_bbs.insert(srcbb);

                for (auto dist_target : dist_bb_to_one_target_bb[vbb]) {
                    const SVFBasicBlock* target_bb = dist_target.first;
                    uint32_t now_dist = dist_target.second;

                    if ( dist_bb_to_one_target_bb[srcbb].find(target_bb) == dist_bb_to_one_target_bb[srcbb].end() 
                        || dist_bb_to_one_target_bb[srcbb][target_bb] > now_dist + 1 ) {
                        
                        dist_bb_to_one_target_bb[srcbb][target_bb] = now_dist + 1;
                        worklist.push(srcbb);
                    }
                }
			}
		}
	}

    std::cout << "sliced_icfg_bbs: " << sliced_icfg_bbs.size() << std::endl;
    std::cout << "dist_bb_to_one_target_bb: " << dist_bb_to_one_target_bb.size() << std::endl;

    // 结合 bb 能够到达的不同 target 的不同距离，计算 bb 的最终距离
	for (auto bb_item : dist_bb_to_one_target_bb) {
        // bb 的距离为其到 每一个可能到达的 target 的距离的 调和平均数
		double db_tmp = 0;
		bool flag = false;
		for (auto dist_per_target : bb_item.second) {
            db_tmp += (double)1 / (double)dist_per_target.second;
            flag = true;
		}

		if (flag) {
			bb_distance_icfg[bb_item.first] = (double)1/db_tmp;
		}
	}

    // 设置所有 target BB 的最终距离为 0，因为 target_bb 可能到达其他 target,因此距离可能不为0
    for (const SVFBasicBlock* target_bb: targets_svf_bbs) {
        bb_distance_icfg[target_bb] = 0;
    }
}
#endif


#ifndef CRGF_CG_DISTANCE
/**
 * calcCFGDistance 基于每个函数的 CFG 控制流图 计算 BB 到 target 的距离
*/
void calcCFGDistance() {
    std::map<const SVFBasicBlock*, std::map<const SVFBasicBlock*, double>> dist_bb_to_callsite_bbs;

    std::cout << "pre_tainted_callsite_bbs: " << pre_tainted_callsite_bbs.size() << std::endl;

    // 污染其他没有直接调用 slice func 的基本块
	for (const SVFBasicBlock* callsite : pre_tainted_callsite_bbs) {

		FIFOWorkList<const SVFBasicBlock*> worklist;
		worklist.push(callsite);
        dist_bb_to_callsite_bbs[callsite][callsite] = bb_distance_icfg[callsite];

		while (!worklist.empty())
		{
			const SVFBasicBlock* vbb = worklist.pop();

			for (const SVFBasicBlock* srcbb : vbb->getPredecessors()) {
                double now_dist = dist_bb_to_callsite_bbs[vbb][callsite] + 1;

                if ( dist_bb_to_callsite_bbs[srcbb].find(callsite) == dist_bb_to_callsite_bbs[srcbb].end() 
                    || dist_bb_to_callsite_bbs[srcbb][callsite] > now_dist ) {
                    
                    dist_bb_to_callsite_bbs[srcbb][callsite] =  now_dist;
                    worklist.push(srcbb);
                }
			}
		}
	}

    std::cout << "dist_bb_to_callsite_bbs: " << dist_bb_to_callsite_bbs.size() << std::endl;

    // 结合 bb 能够到达的不同 target 的不同距离，计算 bb 的最终距离
	for (auto bb_item : dist_bb_to_callsite_bbs) {
        // bb 的距离为其到 每一个可能到达的 target 的距离的 调和平均数
		double dis = 0;
		for (auto callsite_bb : bb_item.second) {
            dis += (double)1 / (double)callsite_bb.second;
		}

		if (dis > 0) {
			bb_distance_icfg[bb_item.first] = (double)1 / dis;
		}
	}

    // 设置所有 target BB 的最终距离为 0，因为 target_bb 可能到达其他 target,因此距离可能不为0
    for (const SVFBasicBlock* target_bb: targets_svf_bbs) {
        bb_distance_icfg[target_bb] = 0;
    }
}
#endif


void postAnalysisInstExcludeBB() {
    for (const SVFBasicBlock* bb : sliced_icfg_bbs) {

        // 所有后续基本块在切片中，就可以排除此基本块
        bool all_succ_in = true;
        for (const SVFBasicBlock* sussBB : bb->getSuccessors()) {
            if (sliced_icfg_bbs.find(sussBB) == sliced_icfg_bbs.end()) {
                all_succ_in = false;
            }
        }

        if (bb->getNumSuccessors() > 0 && all_succ_in) {
            // 插桩的时候就可以排除
            inst_exclude_bbs_backward_icfg.insert(bb);
        }
    }
}


void calcDistance() {
    std::cout << "Start Calc Distance..." << std::endl;
    // should loadTargets() first

    std::cout << "Calc Call-Graph Reaching..." << std::endl;
    // 统计所有可达函数
    calcCallGraphReaching();

    std::cout << "Pre Slice all callsites BBs..." << std::endl;
    // 再次遍历CG, 记录所有 callsites
    preSliceCallsiteBBs();

#ifdef CRGF_CG_DISTANCE
    std::cout << "Calc Func-entry to BB distance..." << std::endl;
    // 计算可达函数中所有 bb 到函数入口处的最短距离
    calcFuncEntry2SliceBBDistance();
#endif

    std::cout << "Calc Call-Graph distance..." << std::endl;
    // 计算函数间距离，根据函数调用图，结合前面函数入口到基本块距离
    // 计算出来的是真正的基本块数量，而不是粗略的函数数量
    calcCallGraphDistance();

    std::cout << "Calc per-Func BB distance..." << std::endl;
    calcCFGDistance();

    // 目标基本块距离为 0
    for (const SVFBasicBlock* target_bb : targets_svf_bbs) {
        bb_distance_icfg[target_bb] = 0;
    }

    std::cout << "End Calc Distance !" << std::endl;
}


bool inAllSliceBB(const SVFBasicBlock* bb) {
    return (
        sliced_icfg_bbs.find(bb) != sliced_icfg_bbs.end()
        || backward_slice_pure_svf_icfg_bbs.find(bb) != backward_slice_pure_svf_icfg_bbs.end()
    );
}

/**
 * 后向分析，确定偏差块
*/
void backwardIdentifyCriticalBB() {
    std::set<const SVFBasicBlock*> tmp_early_exit_bbs;

    // 后向分析
    for (const SVFBasicBlock* BB : sliced_icfg_bbs ) {
        std::set<const SVFBasicBlock*> tmp_exit_bbs;
        std::set<const SVFBasicBlock*> tmp_solved_bbs;

        /* 有多个后继，说明是分支块，可能导向非切片块 */
        if ( BB->getNumSuccessors() >= 2 ) {
            for ( const SVFBasicBlock* succBB : BB->getSuccessors() ) {
                if ( !inAllSliceBB(succBB) ) {
                    /* 包含一个非切片后继 BB */
                    tmp_exit_bbs.insert( succBB );
                } else {
                    tmp_solved_bbs.insert( succBB );
                }
            }
        }

        if ( !tmp_exit_bbs.empty() ) {
            critical_bbs.insert(BB);

            critical_exit_bbs_map[ BB ] = tmp_exit_bbs;
            critical_solved_bbs_map[ BB ]   = tmp_solved_bbs;

            tmp_early_exit_bbs.insert(tmp_exit_bbs.begin(), tmp_exit_bbs.end());
        }
    }

    // 对于 early exit bb, 需要保证这些 bb 不是在前向的函数切片中，避免影响target 后的继续执行
    for (const SVFBasicBlock* bb: tmp_early_exit_bbs) {
        const SVFFunction* func = bb->getFunction();

        // 对于前向可达函数中的 bb，不进行 early exit， 所以要进行跳过
        if (func != nullptr && func_from_target_continue.find(func) != func_from_target_continue.end()) {
            continue;
        }

        early_exit_bb.insert(bb);
    }

    std::cout << "[Critical BB] critical BBs count: " << critical_bbs.size() << std::endl;
    std::cout << "[Critical BB] early exit BBs count: " << early_exit_bb.size() << std::endl;
}



void preProcessAllSVFGNode() {
    int count = 0;
    for ( auto it = svfg->begin(), ite = svfg->end(); it != ite; ++it ) {
        SVFGNode* node = it->second;
        // std::cout << "\nID: " << node->getId() << "\tfun: " << ( node->getFun() ? node->getFun()->getName() :
        // "noFunc" )
        //           << "\tnode kind: " << node->getNodeKind() << std::endl;
        const SVFValue* svalue = node->getValue();
        if ( svalue == nullptr ) {
            // std::cout << "Not a SVFValue" << std::endl;
            continue;
        }

        // 记录 SVFG Node 与 SVF Value 的关系，SVF Value 可以与 LLVM Value 互相转换
        svfvalue_svfgnode[ svalue ] = node;

        if ( SVFUtil::isa<SVFInstruction>( svalue ) ) {
            const SVFInstruction* sinst = SVFUtil::dyn_cast<SVFInstruction>( svalue );
            count++;
            // std::cout << "Is a SVFInstruction: " << sinst->toString() << std::endl;
        } else {
            // std::cout << "SVFValue not a SVFInstruction:\t" << svalue->getKind() << std::endl;
        }
    }
    std::cout << "preProcessAllSVFGNode: " << count << std::endl;
}

void countBBs() {
    int total_bbs = 0;
    for ( Function& F : *LLVM_M ) {
        for ( BasicBlock& BB : F ) {
            total_bbs++;
        }
    }
    std::cout << "ALL total bbs: " << total_bbs << std::endl;

    std::cout << "[Slice] forward  SVFG BB count: " << forward_slice_svfg_bbs.size() << std::endl;
    std::cout << "[Slice] backward SVFG BB count: " << backward_slice_svfg_bbs.size() << std::endl;
    std::cout << "[Slice] backward ICFG BB count: " << backward_slice_pure_svf_icfg_bbs.size() << std::endl;
}

void dumpSlice2txt() {
    auto LM = LLVMModuleSet::getLLVMModuleSet();

    std::cout << std::endl << "Start Dump Slice BB to txt..." << std::endl;
    ofstream f_slice_bbs( "slice_bbs.txt", std::ios::out );

    // 数据流 SVFG ==================================================
    // dump slice (df: back/forward) only for debug
    ofstream f_debug_slice_forward_df( "DEBUG_slice_forward_df.txt", std::ios::out );
    ofstream f_debug_slice_backward_df( "DEBUG_slice_backward_df.txt", std::ios::out );
    for ( auto bb : forward_slice_svfg_bbs ) {
        auto loc = getDebugInfo( bb );
        f_debug_slice_forward_df << loc << std::endl;
    }
    for ( auto bb : backward_slice_svfg_bbs ) {
        auto loc = getDebugInfo( bb );
        f_debug_slice_backward_df << loc << std::endl;
    }

    // 后向 backward SVFG 
    std::cout << "Dump Backward Slice BB distance to txt..." << std::endl;
    ofstream f_debug_backward_bb_distance_svfg( "DEBUG_backward_bb_distance_svfg.txt", std::ios::out ); // debug
    ofstream f_backward_distance_svfg( "backward_distance_svfg.txt", std::ios::out ); // fuzz use
    for ( auto bb : bb_distance_backward_svfg ) {
        auto loc = getDebugInfo( bb.first );
        f_debug_backward_bb_distance_svfg << loc << ":" << bb.second << std::endl;

        std::string FileName; unsigned Line;
        if (!getDebugLocOfBB( bb.first, FileName, Line )) continue;
        f_backward_distance_svfg << FileName << ":" << Line << "," << bb.second << std::endl;

        f_slice_bbs << FileName << ":" << Line << std::endl;
    }


    // 前向 Forward
    std::cout << "Dump Forward Slice BB distance to txt..." << std::endl;
    ofstream f_debug_forward_bb_depth( "DEBUG_forward_bb_depth.txt", std::ios::out );
    ofstream f_forward_depth( "forward_depth.txt", std::ios::out );

    for ( auto bb : bb_distance_forward_svfg ) {
        auto loc = getDebugInfo( bb.first );
        f_debug_forward_bb_depth << loc << ":" << bb.second << std::endl;

        std::string FileName; unsigned Line;
        if (!getDebugLocOfBB( bb.first, FileName, Line )) continue;
        f_forward_depth << FileName << ":" << Line<< "," << bb.second << std::endl;

        f_slice_bbs << FileName << ":" << Line << std::endl;
    }

    // 数据流结束 ==================================================




    // 控制流 ICFG ==================================================

    // 后向 Backward
    std::cout << "Dump Backward ICFG Slice BB distance to txt..." << std::endl;
    ofstream f_debug_backward_bb_distance_icfg( "DEBUG_backward_bb_distance_icfg.txt", std::ios::out ); // for debug

    // 开始按照行号去重，取行内最小的距离
    std::map<string, double> bb_distance_icfg_dedup;
    for ( auto bb : bb_distance_icfg ) {
        BasicBlock* BB = const_cast<BasicBlock*>( dyn_cast<llvm::BasicBlock>( LM->getLLVMValue( bb.first ) ) );
        auto loc = getDebugInfo( BB );
        f_debug_backward_bb_distance_icfg << loc << ":" << bb.second << std::endl;

        std::string FileName; unsigned Line;
        if (!getDebugLocOfBB( BB, FileName, Line )) continue;

        std::stringstream ss;
        ss << FileName << ":" << Line;
        std::string pos = ss.str();

        if (bb_distance_icfg_dedup.find(pos) != bb_distance_icfg_dedup.end()
           && bb_distance_icfg_dedup[pos] > bb.second) {
        
            bb_distance_icfg_dedup[pos] = bb.second;
        } else {
            bb_distance_icfg_dedup[pos] = bb.second;
        }
    }
    // 输出按行号去重后的距离
    ofstream f_backward_distance_icfg( "backward_distance_icfg.txt", std::ios::out ); // for use
    for ( auto bb : bb_distance_icfg_dedup ) {
        // for fuzz use
        f_backward_distance_icfg << bb.first << "," << bb.second << std::endl;
        // add to slice
        f_slice_bbs << bb.first << std::endl;
    }

    // icfg 插桩时需要去除的节点，因为其后续节点信息足够使用
    ofstream f_inst_exclude_icfg( "inst_exclude_icfg.txt", std::ios::out ); // for use
    for ( auto bb : inst_exclude_bbs_backward_icfg ) {
        BasicBlock* BB = const_cast<BasicBlock*>( dyn_cast<llvm::BasicBlock>( LM->getLLVMValue( bb ) ) );

        std::string FileName; unsigned Line;
        if (!getDebugLocOfBB( BB, FileName, Line )) continue;

        f_inst_exclude_icfg << FileName << ":" << Line << std::endl;
    }

    // 控制流 结束 ==================================================


    std::cout << "Dump Target BBs to txt..." << std::endl;
    ofstream f_target_bbs( "target_bbs.txt", std::ios::out );
    for ( auto bb : targets_llvm_bb ) {
        std::string FileName; unsigned Line;
        if (!getDebugLocOfBB( bb, FileName, Line )) continue;
        f_target_bbs << FileName << ":" << Line << std::endl;
    }
    

    std::cout << "Dump Early Exit BBs to txt..." << std::endl;
    ofstream f_early_exit_bbs( "early_exit_bbs.txt", std::ios::out );
    for ( auto bb : early_exit_bb ) {
        BasicBlock* BB = const_cast<BasicBlock*>( dyn_cast<llvm::BasicBlock>( LM->getLLVMValue( bb ) ) );

        std::string FileName; unsigned Line;
        if (!getDebugLocOfBB( BB, FileName, Line )) continue;
        f_early_exit_bbs << FileName << ":" << Line << std::endl;
    }

    std::cout << "Dump Function level distance to txt..." << std::endl;
    ofstream f_debug_dist_func( "DEBUG_dist_func.txt", std::ios::out );
    for (auto func : func_distance_icfg) {
        BasicBlock* BB = const_cast<BasicBlock*>( dyn_cast<llvm::BasicBlock>( LM->getLLVMValue( func.first->getEntryBlock() ) ) );
        auto loc = getDebugInfo( BB );
        f_debug_dist_func << loc << ":" << func.second << std::endl;
    }
    
}

void checkSlice() {
    // 检查后向控制流切片是否到达了开始的 main 函数
    bool slice_include_main = false;
    const SVFFunction* svf_func_main;
    for (auto func : func_reach_target) {
        if (func->getName() == "main") {
            slice_include_main = true;
            svf_func_main = func;
            break;
        }
    }
    std::cout << "Slice include func main: " << slice_include_main << std::endl;

    // 检查 main 函数 entry bb 是否被切片
    bool slice_include_main_entry_bb = false;
    if (slice_include_main) {
        const SVFBasicBlock* entry = svf_func_main->getEntryBlock();
        if (bb_distance_icfg.find(entry) != bb_distance_icfg.end()) {
            slice_include_main_entry_bb = true;
            std::cout << "Slice include main entry BB: True !" << std::endl;
        } else {
             std::cout << "Slice include main entry BB: False !" << std::endl;
        }
    }


    // 检查 不同 SVFBasicBlock 对应同一个 LLVM BB 的情况
    // 应该是没有输出的才对，就是说不应该有 llvm bb 对应多个 svf bb
    // 而结果中的行号的距离不同，是因为代码中使用 define 将多个基本块放到一行中了，例如 forloop 用宏来简写
    std::map<BasicBlock*, std::vector<const SVFBasicBlock*>> bbmap;
    auto LM = LLVMModuleSet::getLLVMModuleSet();
    for ( auto bb : bb_distance_icfg ) {
        BasicBlock* BB = const_cast<BasicBlock*>( dyn_cast<llvm::BasicBlock>( LM->getLLVMValue( bb.first ) ) );
        bbmap[BB].emplace_back(bb.first);
    }

    for (auto bb : bbmap) {
        if (bb.second.size() >= 2) {
            auto loc = getDebugInfo( bb.first );
            std::cout << "Multi SVF_BB to 1 LLVM_BB: " << loc << std::endl;
        }
    }

}

int main( int argc, char** argv ) {

    int                      arg_num   = 0;
    char**                   arg_value = new char*[ argc ];
    std::vector<std::string> moduleNameVec;
    LLVMUtil::processArguments( argc, argv, arg_num, arg_value, moduleNameVec );
    cl::ParseCommandLineOptions( arg_num, arg_value, "Whole Program Points-to Analysis\n" );

    // if ( Options::WriteAnder() == "ir_annotator" ) {
    LLVMModuleSet::getLLVMModuleSet()->preProcessBCs( moduleNameVec );
    // }

    std::cout << "1. build SVFModule" << std::endl;
    svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule( moduleNameVec );

    /// Build Program Assignment Graph (SVFIR)
    /// 创建 PAG
    std::cout << "2. build SVFIR / PAG" << std::endl;
    time_t time_pag_start = time( nullptr );
    SVFIRBuilder builder( svfModule );
    pag = builder.build();
    time_t time_pag_end = time( nullptr );

    /// Create Andersen's pointer analysis
    /// 指针分析
    std::cout << "3. do Andersen's pointer analysis    (may take long time)" << std::endl;
    time_t time_ptr_start = time( nullptr );
    Andersen* ander = AndersenWaveDiff::createAndersenWaveDiff( pag );
    time_t time_ptr_end   = time( nullptr );


    /// Query aliases
    // aliasQuery(ander,value1,value2);

    /// Print points-to information
    /// printPts(ander, value1);

    /// Call Graph
    // std::cout << "4. get PTA CallGraph" << std::endl;
    // callgraph = ander->getPTACallGraph();

    /// ICFG
    /// 跨函数控制流图
    std::cout << "5. get ICFG" << std::endl;
    icfg = ander->getICFG();

    /// Value-Flow Graph (VFG)
    // std::cout << "6. get VFG" << std::endl;
    // VFG* vfg = new VFG( callgraph );

    /// Sparse value-flow graph (SVFG)
    std::cout << "6. build Full SVFG    (may take long time)" << std::endl;
    time_t time_svfg_start = time( nullptr );
    SVFGBuilder svfBuilder;
    svfg = svfBuilder.buildFullSVFG( ander );
    // svfg = svfBuilder.buildPTROnlySVFG( ander );
    time_t time_svfg_end = time( nullptr );

    // update ICFG for indirect call by pointer analysis
    callgraph = svfg->getCallGraph();
    icfg->updateCallGraph(callgraph);


    LLVM_M = LLVMModuleSet::getLLVMModuleSet()->getMainLLVMModule();
    LLVM_C = &LLVMModuleSet::getLLVMModuleSet()->getContext();

    preProcessAllSVFGNode();

    std::cout << "load targets..." << std::endl;
    loadTargets( TargetsFile );

    std::cout << "======================================" << std::endl;
    calcDistance();


    std::cout << "do forward slicing SVFG..." << std::endl;
    forwardSlicingSVFG( targets_svfg_node );

    std::cout << "do backward slicing SVFG..." << std::endl;
    backwardSlicingSVFG( targets_svfg_node );

    std::cout << "do backward slicing ICFG..." << std::endl;
    backwardSlicingICFG();


    countBBs();

    // TODO
    std::cout << "============================" << std::endl;
    std::cout << "Start analysis Critical and Exit bbs ..." << std::endl;
    calcCallGraphContinue(); // 从 target 继续执行可以到达的 func，里面的 bb 不能 early exit
    backwardIdentifyCriticalBB();

    // 筛选可以避免插桩的 BB
    postAnalysisInstExcludeBB();

    // 已经确定所有 SVFG 切出来的块都包含在 ICFG 切出来的块中
    dumpSlice2txt();

    std::cout << std::endl << "===============================" << std::endl;
    // 检查切片是否满足要求
    checkSlice();

    // if ( DoInstrument ) {
    //     std::cout << "Do instrutment..." << std::endl;
    //     instrutment();
    //     std::cout << "instrutment done!" << std::endl;
    // }

    /// ======================================
    // clean up memory
    // skip to speedup, haha

    // AndersenWaveDiff::releaseAndersenWaveDiff();
    // SVFIR::releaseSVFIR();
    // std::cout << "Dump Module BC to .inst.bc" << std::endl;
    // LLVMModuleSet::getLLVMModuleSet()->dumpModulesToFile( ".inst.bc" );
    // SVF::LLVMModuleSet::releaseLLVMModuleSet();
    // llvm::llvm_shutdown();

    std::cout << std::endl << "[Time Statistic]" << std::endl;
    std::cout << time_pag_start << "," << time_pag_end << "," << time_pag_end - time_pag_start << ",";
    std::cout << time_ptr_start << "," << time_ptr_end << "," << time_ptr_end - time_ptr_start << ",";
    std::cout << time_svfg_start << "," << time_svfg_end << "," << time_svfg_end - time_svfg_start << std::endl;

    return 0;
}
