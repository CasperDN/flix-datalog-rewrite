#!/usr/bin/env bash
entrypoint=benchmark
java -jar flix.jar run --entrypoint $entrypoint --args "$1" 
