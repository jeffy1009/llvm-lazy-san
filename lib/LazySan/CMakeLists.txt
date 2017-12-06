set(SOURCES
  LazySan.cpp
    )

add_llvm_library(LLVMLazySan ${SOURCES})
add_dependencies(LLVMLazySan intrinsics_gen)
