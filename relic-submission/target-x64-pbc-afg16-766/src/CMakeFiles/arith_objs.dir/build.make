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
CMAKE_BINARY_DIR = /root/relic-submission/target-x64-pbc-afg16-766

# Utility rule file for arith_objs.

# Include any custom commands dependencies for this target.
include src/CMakeFiles/arith_objs.dir/compiler_depend.make

# Include the progress variables for this target.
include src/CMakeFiles/arith_objs.dir/progress.make

arith_objs: src/CMakeFiles/arith_objs.dir/build.make
.PHONY : arith_objs

# Rule to build all files generated by this target.
src/CMakeFiles/arith_objs.dir/build: arith_objs
.PHONY : src/CMakeFiles/arith_objs.dir/build

src/CMakeFiles/arith_objs.dir/clean:
	cd /root/relic-submission/target-x64-pbc-afg16-766/src && $(CMAKE_COMMAND) -P CMakeFiles/arith_objs.dir/cmake_clean.cmake
.PHONY : src/CMakeFiles/arith_objs.dir/clean

src/CMakeFiles/arith_objs.dir/depend:
	cd /root/relic-submission/target-x64-pbc-afg16-766 && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /root/relic-submission /root/relic-submission/src /root/relic-submission/target-x64-pbc-afg16-766 /root/relic-submission/target-x64-pbc-afg16-766/src /root/relic-submission/target-x64-pbc-afg16-766/src/CMakeFiles/arith_objs.dir/DependInfo.cmake "--color=$(COLOR)"
.PHONY : src/CMakeFiles/arith_objs.dir/depend

