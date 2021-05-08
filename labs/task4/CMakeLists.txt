cmake_minimum_required(VERSION 3.19)
project(task4 C)

set(CMAKE_C_STANDARD 11)

include_directories(.)

add_executable(task4
        map.h
        maptypes.h map.c main.c)
