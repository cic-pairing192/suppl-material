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
CMAKE_BINARY_DIR = /root/relic-submission/target-x64-pbc-fam16-766

# Include any dependencies generated for this target.
include test/CMakeFiles/test_bn.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include test/CMakeFiles/test_bn.dir/compiler_depend.make

# Include the progress variables for this target.
include test/CMakeFiles/test_bn.dir/progress.make

# Include the compile flags for this target's objects.
include test/CMakeFiles/test_bn.dir/flags.make

test/CMakeFiles/test_bn.dir/test_bn.c.o: test/CMakeFiles/test_bn.dir/flags.make
test/CMakeFiles/test_bn.dir/test_bn.c.o: /root/relic-submission/test/test_bn.c
test/CMakeFiles/test_bn.dir/test_bn.c.o: test/CMakeFiles/test_bn.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --progress-dir=/root/relic-submission/target-x64-pbc-fam16-766/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building C object test/CMakeFiles/test_bn.dir/test_bn.c.o"
	cd /root/relic-submission/target-x64-pbc-fam16-766/test && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -MD -MT test/CMakeFiles/test_bn.dir/test_bn.c.o -MF CMakeFiles/test_bn.dir/test_bn.c.o.d -o CMakeFiles/test_bn.dir/test_bn.c.o -c /root/relic-submission/test/test_bn.c

test/CMakeFiles/test_bn.dir/test_bn.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Preprocessing C source to CMakeFiles/test_bn.dir/test_bn.c.i"
	cd /root/relic-submission/target-x64-pbc-fam16-766/test && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /root/relic-submission/test/test_bn.c > CMakeFiles/test_bn.dir/test_bn.c.i

test/CMakeFiles/test_bn.dir/test_bn.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Compiling C source to assembly CMakeFiles/test_bn.dir/test_bn.c.s"
	cd /root/relic-submission/target-x64-pbc-fam16-766/test && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /root/relic-submission/test/test_bn.c -o CMakeFiles/test_bn.dir/test_bn.c.s

# Object files for target test_bn
test_bn_OBJECTS = \
"CMakeFiles/test_bn.dir/test_bn.c.o"

# External object files for target test_bn
test_bn_EXTERNAL_OBJECTS =

bin/test_bn: test/CMakeFiles/test_bn.dir/test_bn.c.o
bin/test_bn: test/CMakeFiles/test_bn.dir/build.make
bin/test_bn: lib/librelic_s.a
bin/test_bn: /usr/lib/libgmp.a
bin/test_bn: test/CMakeFiles/test_bn.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --bold --progress-dir=/root/relic-submission/target-x64-pbc-fam16-766/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking C executable ../bin/test_bn"
	cd /root/relic-submission/target-x64-pbc-fam16-766/test && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/test_bn.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
test/CMakeFiles/test_bn.dir/build: bin/test_bn
.PHONY : test/CMakeFiles/test_bn.dir/build

test/CMakeFiles/test_bn.dir/clean:
	cd /root/relic-submission/target-x64-pbc-fam16-766/test && $(CMAKE_COMMAND) -P CMakeFiles/test_bn.dir/cmake_clean.cmake
.PHONY : test/CMakeFiles/test_bn.dir/clean

test/CMakeFiles/test_bn.dir/depend:
	cd /root/relic-submission/target-x64-pbc-fam16-766 && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /root/relic-submission /root/relic-submission/test /root/relic-submission/target-x64-pbc-fam16-766 /root/relic-submission/target-x64-pbc-fam16-766/test /root/relic-submission/target-x64-pbc-fam16-766/test/CMakeFiles/test_bn.dir/DependInfo.cmake "--color=$(COLOR)"
.PHONY : test/CMakeFiles/test_bn.dir/depend

