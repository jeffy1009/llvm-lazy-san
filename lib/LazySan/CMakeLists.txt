include_directories(${CMAKE_SOURCE_DIR}/projects/poolalloc/include)

set(SOURCES
  LazySan.cpp
    )

add_llvm_library(LLVMLazySan
  ${SOURCES}

  LINK_LIBS
  LLVMDataStructure_static
  )

add_dependencies(LLVMLazySan intrinsics_gen)
