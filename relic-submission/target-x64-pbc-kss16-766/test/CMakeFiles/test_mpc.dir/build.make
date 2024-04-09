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
CMAKE_BINARY_DIR = /root/relic-submission/target-x64-pbc-kss16-766

# Include any dependencies generated for this target.
include test/CMakeFiles/test_mpc.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include test/CMakeFiles/test_mpc.dir/compiler_depend.make

# Include the progress variables for this target.
include test/CMakeFiles/test_mpc.dir/progress.make

# Include the compile flags for this target's objects.
include test/CMakeFiles/test_mpc.dir/flags.make

test/CMakeFiles/test_mpc.dir/test_mpc.c.o: test/CMakeFiles/test_mpc.dir/flags.make
test/CMakeFiles/test_mpc.dir/test_mpc.c.o: /root/relic-submission/test/test_mpc.c
test/CMakeFiles/test_mpc.dir/test_mpc.c.o: test/CMakeFiles/test_mpc.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --progress-dir=/root/relic-submission/target-x64-pbc-kss16-766/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building C object test/CMakeFiles/test_mpc.dir/test_mpc.c.o"
	cd /root/relic-submission/target-x64-pbc-kss16-766/test && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -MD -MT test/CMakeFiles/test_mpc.dir/test_mpc.c.o -MF CMakeFiles/test_mpc.dir/test_mpc.c.o.d -o CMakeFiles/test_mpc.dir/test_mpc.c.o -c /root/relic-submission/test/test_mpc.c

test/CMakeFiles/test_mpc.dir/test_mpc.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Preprocessing C source to CMakeFiles/test_mpc.dir/test_mpc.c.i"
	cd /root/relic-submission/target-x64-pbc-kss16-766/test && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /root/relic-submission/test/test_mpc.c > CMakeFiles/test_mpc.dir/test_mpc.c.i

test/CMakeFiles/test_mpc.dir/test_mpc.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Compiling C source to assembly CMakeFiles/test_mpc.dir/test_mpc.c.s"
	cd /root/relic-submission/target-x64-pbc-kss16-766/test && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /root/relic-submission/test/test_mpc.c -o CMakeFiles/test_mpc.dir/test_mpc.c.s

# Object files for target test_mpc
test_mpc_OBJECTS = \
"CMakeFiles/test_mpc.dir/test_mpc.c.o"

# External object files for target test_mpc
test_mpc_EXTERNAL_OBJECTS =

bin/test_mpc: test/CMakeFiles/test_mpc.dir/test_mpc.c.o
bin/test_mpc: test/CMakeFiles/test_mpc.dir/build.make
bin/test_mpc: lib/librelic_s.a
bin/test_mpc: /usr/lib/libgmp.a
bin/test_mpc: test/CMakeFiles/test_mpc.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --bold --progress-dir=/root/relic-submission/target-x64-pbc-kss16-766/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking C executable ../bin/test_mpc"
	cd /root/relic-submission/target-x64-pbc-kss16-766/test && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/test_mpc.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
test/CMakeFiles/test_mpc.dir/build: bin/test_mpc
.PHONY : test/CMakeFiles/test_mpc.dir/build

test/CMakeFiles/test_mpc.dir/clean:
	cd /root/relic-submission/target-x64-pbc-kss16-766/test && $(CMAKE_COMMAND) -P CMakeFiles/test_mpc.dir/cmake_clean.cmake
.PHONY : test/CMakeFiles/test_mpc.dir/clean

test/CMakeFiles/test_mpc.dir/depend:
	cd /root/relic-submission/target-x64-pbc-kss16-766 && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /root/relic-submission /root/relic-submission/test /root/relic-submission/target-x64-pbc-kss16-766 /root/relic-submission/target-x64-pbc-kss16-766/test /root/relic-submission/target-x64-pbc-kss16-766/test/CMakeFiles/test_mpc.dir/DependInfo.cmake "--color=$(COLOR)"
.PHONY : test/CMakeFiles/test_mpc.dir/depend

