#!/bin/bash

today=`date +%Y-%m-%d.%H:%M:%S`

git add -A
git commit -m "$today"
git push origin master
