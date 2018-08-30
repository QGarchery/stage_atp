#!/bin/bash

map () {
    for i in $(cat)
    do $1 $i
    done
}

