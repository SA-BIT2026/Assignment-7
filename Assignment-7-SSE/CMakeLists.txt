add_library(a7lib SSEZ3Mgr.cpp SSELib.cpp)
target_link_libraries(a7lib PRIVATE
        ${Z3_LIBRARIES}
        )

add_executable(sse SSE.cpp)
target_link_libraries(sse PRIVATE
        ${SVF_LIB}
        ${LLVM_LIB}
        ${Z3_LIBRARIES}
        a7lib
        )
set_target_properties(sse PROPERTIES
        RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})