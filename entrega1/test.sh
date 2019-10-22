#!/bin/sh

TEST=../tests # complete with the path to the tests folder

GOOD=${TEST}/good
SYNTAX=${TEST}/syntax
TYPE=${TEST}/type

eval_test () {
    for d in $1/* ; do
        if ./tiger $d | grep -q "bien!" ; then
            echo "$(tput setaf 2)[ok] $(tput sgr 0) $d"
        else
            echo "$(tput setaf 1)[err] $(tput sgr 0) $d"
        fi   
    done
}

eval_test ${GOOD}
eval_test ${SYNTAX}
eval_test ${TYPE}

