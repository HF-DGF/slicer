llvm_map_components_to_libnames(llvm_libs bitwriter core ipo irreader instcombine instrumentation target linker analysis scalaropts support )
file (GLOB SOURCES
   *.cpp
)

# 使用 CRGF 的函数级别距离计算
# add_definitions(-DCRGF_CG_DISTANCE)
if (DEFINED ENV{AFLGOCG})
    message("AFLGOCG is defined")
else()
    # 如果不存在，添加定义-DCRGF_CG_DISTANCE
    message("AFLGOCG is not defined. Adding -DCRGF_CG_DISTANCE")
    add_definitions(-DCRGF_CG_DISTANCE)
endif()

add_executable(slicer ${SOURCES})

target_link_libraries(slicer ${SVF_LIB} ${llvm_libs})
target_link_libraries(slicer ${Z3_LIBRARIES})
set_target_properties( slicer PROPERTIES
                       RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
