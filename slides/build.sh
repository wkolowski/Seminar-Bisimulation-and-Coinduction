#!/bin/sh
find . -name "*.tex" -exec latexmk -pdf -interaction=nonstopmode {} \;
