#!/bin/bash

clear

echo -e "=====APPLIED SECURITY - COURSEWORK 1 AUTOTESTER====="
echo
echo -e "=====COMPILING====="
make clean
make
if [ $? -eq 0 ]; then
  echo -e "[\xE2\x9C\x93] Compilation completed successfully."
else
  echo "[X] Compilation failed!"
  exit 1
fi
echo

echo -e "=====Stage 1 test====="
time ./modmul stage1 < stage1.input > test1.output
echo
file1=`sha1sum test1.output | awk '{ print $1 }'`
file2=`sha1sum stage1.output | awk '{ print $1 }'`
if [ "$file1" == "$file2" ]; then
  echo -e "[\xE2\x9C\x93] Stage 1 test successful."
else
  echo -e "[X] Stage 1 test failed!"
fi
echo

echo -e "=====Stage 2 test====="
#time (for i in {1..10000}; do ./modmul stage2 < stage2.input > test2.output ; done)
time ./modmul stage2 < stage2.input > test2.output
echo
file1=`sha1sum test2.output | awk '{ print $1 }'`
file2=`sha1sum stage2.output | awk '{ print $1 }'`
if [ "$file1" == "$file2" ]; then
  echo -e "[\xE2\x9C\x93] Stage 2 test successful."
else
  echo -e "[X] Stage 2 test failed!"
fi
echo

echo -e "=====Stage 3 test====="
time ./modmul stage3 testing < stage3.input > test3.output
echo
file1=`sha1sum test3.output | awk '{ print $1 }'`
file2=`sha1sum stage3.output | awk '{ print $1 }'`
if [ "$file1" == "$file2" ]; then
  echo -e "[\xE2\x9C\x93] Stage 3 test successful."
else
  echo -e "[X] Stage 3 test failed!"
fi
echo

echo -e "=====Stage 4 test====="
time ./modmul stage4 < stage4.input > test4.output
echo
file1=`sha1sum test4.output | awk '{ print $1 }'`
file2=`sha1sum stage4.output | awk '{ print $1 }'`
if [ "$file1" == "$file2" ]; then
  echo -e "[\xE2\x9C\x93] Stage 4 test successful."
else
  echo -e "[X] Stage 4 test failed!"
fi
echo
