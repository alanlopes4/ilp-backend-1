#!/usr/bin/env bash

programas=('bmm' 'Bubblesort' 'chomp' 'drop3' 'dry' 'md5' 'flops-1' 'gemm' 'huffbench' 'lpbench')

for p in ${programas[@]}
    do
        echo "PROGRAMA: ${p}"
        make clean; 
        if [[ $p == "gemm" ]]; then make test PROGRAMA=programas/$p/$p.c DEP=programas/$p 
        else make test PROGRAMA=programas/$p/$p.c
        fi
    done
