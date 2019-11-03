#!/bin/bash

TEST_DIR=../tests # complete path to tests directory

GOOD_DIR=${TEST_DIR}/good
SYNTAX_DIR=${TEST_DIR}/syntax
TYPE_DIR=${TEST_DIR}/type

eval_test ()
{
    FILE_COUNT=0
    OK_COUNT=0
    for d in $1/* ; do
	FILE_COUNT=$((FILE_COUNT+1))
        if ./tiger $d | grep -q "bien!" ; then
	    OK_COUNT=$((OK_COUNT+1))
            echo "$(tput setaf 2)[ok] $(tput sgr 0) $d"
        else
            echo "$(tput setaf 1)[err] $(tput sgr 0) $d"
	    ./tiger $d
        fi
    done
    echo "Result ${OK_COUNT}/${FILE_COUNT} (ok/number of files)"
}

usage()
{
    echo "[-h | --help]    print 'this' help"
    echo "[-g | --good]    to test tiger's files in ${GOOD_DIR}"
    echo "[-s | --syntax]  to test tiger's files in ${SYNTAX_DIR}"
    echo "[-t | --type]    to test tiger's files in ${TYPE_DIR}"
    echo "no paramerts test tiger's files in ${GOOD_DIR} ${SYNTAX_DIR} ${TYPE_DIR}"
}

if [ $# -gt 0 ]; then
    while [ "$1" != "" ]; do
	case "$1" in        # match the argument with the options
	    -g | --good)    eval_test ${GOOD_DIR}
			    ;;
	    -s | --syntax)  eval_test ${SYNTAX_DIR}
			    ;;
	    -t | --type)    eval_test ${TYPE_DIR}
			    ;;
	    -h | --help)    usage
			    exit 1
			    ;;
	    * )             usage
			    exit 1
	esac
	shift               # position in the next argument
    done
else
    # no arguments run all test
    eval_test ${GOOD_DIR}
    eval_test ${SYNTAX_DIR}
    eval_test ${TYPE_DIR}
fi
