#!/usr/bin/env bash

###############################################################
#
# Usage:
# In the dependency-graph folder, [generate-dpegraph.sh myname]
# produces [myname.dot], [myname.png] and [myname.svg].
#
# Example:
# cd dependency-graph
# ./generate-depgraph.sh depgraph-2020-09-24
#
# Requires: graphviz for .dot to .png/.svg generation,
# a recent bash (not the one shipped with OS X Catalina for example)
###############################################################


filename=deps
dot_file=$filename.dot

# Associative arrays of the folders together with a color
declare -A folders
folders[API]=tan
folders[Preprocess]=lemonchiffon1
folders[CustomParam]=lightblue
folders[Recursors]=pink

# Two first lines
echo "digraph dependencies {" > deps.dot
echo "node[style=filled]" >> deps.dot
for folder in "${!folders[@]}"
do  coqdep -Q . RecAPI $folder/*.v UnitTests/unit_tests.v |
    # Only keep deps
    sed -n -e 's,/,.,g;s/[.]vo.*: [^ ]*[.]v//p' |
    # Add colors and Arrows
    while read src dst; do
        color=${folders[$folder]}
        echo "\"$src\" [fillcolor=$color];" >> deps.dot
        for d in $dst; do
        echo "\"${d%.vo}\" -> \"$src\" ;" >> deps.dot
        done
    done;
done

# remove duplicate lines
awk '!a[$0]++' deps.dot > deps.dot.tmp && mv -f deps.dot.tmp deps.dot

# simplify names
for folder in "${!folders[@]}"
do
  sed -i -e "s,$folder.,,g" deps.dot
done

# last line
echo "}" >> deps.dot

# remove transitivity and produce the png file
tred deps.dot | dot -T png > deps.png


