# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.28

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Disable VCS-based implicit rules.
% : %,v

# Disable VCS-based implicit rules.
% : RCS/%

# Disable VCS-based implicit rules.
% : RCS/%,v

# Disable VCS-based implicit rules.
% : SCCS/s.%

# Disable VCS-based implicit rules.
% : s.%

.SUFFIXES: .hpux_make_needs_suffix_list

# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /root/relic-submission

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /root/relic-submission/target-x64-pbc-bls24-509

# Include any dependencies generated for this target.
include test/CMakeFiles/test_fpx.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include test/CMakeFiles/test_fpx.dir/compiler_depend.make

# Include the progress variables for this target.
include test/CMakeFiles/test_fpx.dir/progress.make

# Include the compile flags for this target's objects.
include test/CMakeFiles/test_fpx.dir/flags.make

test/CMakeFiles/test_fpx.dir/test_fpx.c.o: test/CMakeFiles/test_fpx.dir/flags.make
test/CMakeFiles/test_fpx.dir/test_fpx.c.o: /root/relic-submission/test/test_fpx.c
test/CMakeFiles/test_fpx.dir/test_fpx.c.o: test/CMakeFiles/test_fpx.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --progress-dir=/root/relic-submission/target-x64-pbc-bls24-509/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building C object test/CMakeFiles/test_fpx.dir/test_fpx.c.o"
	cd /root/relic-submission/target-x64-pbc-bls24-509/test && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -MD -MT test/CMakeFiles/test_fpx.dir/test_fpx.c.o -MF CMakeFiles/test_fpx.dir/test_fpx.c.o.d -o CMakeFiles/test_fpx.dir/test_fpx.c.o -c /root/relic-submission/test/test_fpx.c

test/CMakeFiles/test_fpx.dir/test_fpx.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Preprocessing C source to CMakeFiles/test_fpx.dir/test_fpx.c.i"
	cd /root/relic-submission/target-x64-pbc-bls24-509/test && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /root/relic-submission/test/test_fpx.c > CMakeFiles/test_fpx.dir/test_fpx.c.i

test/CMakeFiles/test_fpx.dir/test_fpx.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Compiling C source to assembly CMakeFiles/test_fpx.dir/test_fpx.c.s"
	cd /root/relic-submission/target-x64-pbc-bls24-509/test && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /root/relic-submission/test/test_fpx.c -o CMakeFiles/test_fpx.dir/test_fpx.c.s

# Object files for target test_fpx
test_fpx_OBJECTS = \
"CMakeFiles/test_fpx.dir/test_fpx.c.o"

# External object files for target test_fpx
test_fpx_EXTERNAL_OBJECTS =

bin/test_fpx: test/CMakeFiles/test_fpx.dir/test_fpx.c.o
bin/test_fpx: test/CMakeFiles/test_fpx.dir/build.make
bin/test_fpx: lib/librelic_s.a
bin/test_fpx: /usr/lib/libgmp.a
bin/test_fpx: test/CMakeFiles/test_fpx.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --bold --progress-dir=/root/relic-submission/target-x64-pbc-bls24-509/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking C executable ../bin/test_fpx"
	cd /root/relic-submission/target-x64-pbc-bls24-509/test && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/test_fpx.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
test/CMakeFiles/test_fpx.dir/build: bin/test_fpx
.PHONY : test/CMakeFiles/test_fpx.dir/build

test/CMakeFiles/test_fpx.dir/clean:
	cd /root/relic-submission/target-x64-pbc-bls24-509/test && $(CMAKE_COMMAND) -P CMakeFiles/test_fpx.dir/cmake_clean.cmake
.PHONY : test/CMakeFiles/test_fpx.dir/clean

test/CMakeFiles/test_fpx.dir/depend:
	cd /root/relic-submission/target-x64-pbc-bls24-509 && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /root/relic-submission /root/relic-submission/test /root/relic-submission/target-x64-pbc-bls24-509 /root/relic-submission/target-x64-pbc-bls24-509/test /root/relic-submission/target-x64-pbc-bls24-509/test/CMakeFiles/test_fpx.dir/DependInfo.cmake "--color=$(COLOR)"
.PHONY : test/CMakeFiles/test_fpx.dir/depend

