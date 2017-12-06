set(SOURCES
  ls_interposer_rt.c
    )

set(CMAKE_EXE_LINKER_FLAGS
    "${CMAKE_EXE_LINKER_FLAGS} -ldl")

add_llvm_loadable_module(ls_interposer_rt
  ${SOURCES}
    )
