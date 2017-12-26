set(SOURCES
  ls_interposer_rt.c
  red_black_tree.c
    )

add_llvm_loadable_module(ls_interposer_rt
  ${SOURCES}
    )

target_link_libraries(ls_interposer_rt dl)
