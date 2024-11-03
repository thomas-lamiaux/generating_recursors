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


filename=../deps
dot_file=$filename.dot

# Associative arrays of the folders together with a color
declare -A folders
folders[API]=tan
folders[Preprocess]=lemonchiffon1
folders[CustomParam]=lightblue
folders[Recursors]=pink
folders[Functoriality]=mediumpurple1

# Two first lines
cd recursors_api/

echo "digraph dependencies {" > $dot_file
echo "node[style=filled]" >> $dot_file
for folder in "${!folders[@]}"
do  coqdep -Q . RecAPI $folder/*.v |
    # Only keep deps
    sed -n -e 's,/,.,g;s/[.]vo.*: [^ ]*[.]v//p' |
    # Add colors and Arrows
    while read src dst; do
        color=${folders[$folder]}
        echo "\"$src\" [fillcolor=$color];" >> $dot_file
        for d in $dst; do
        echo "\"${d%.vo}\" -> \"$src\" ;" >> $dot_file
        done
    done;
done

# Unit Test
coqdep -Q . RecAPI UnitTests/unit_tests.v |
  # Only keep deps
  sed -n -e 's,/,.,g;s/[.]vo.*: [^ ]*[.]v//p' |
  # Add colors and Arrows
  while read src dst; do
      color=chartreuse2
      echo "\"$src\" [fillcolor=$color];" >> $dot_file
      for d in $dst; do
      echo "\"${d%.vo}\" -> \"$src\" ;" >> $dot_file
      done
  done;

# remove duplicate lines
awk '!a[$0]++' $dot_file > $dot_file.tmp && mv -f $dot_file.tmp $dot_file

# simplify names
for folder in "${!folders[@]}"
do
  sed -i -e "s,$folder.,,g" $dot_file
done
sed -i -e "s,UnitTests.,,g" $dot_file

# last line
echo "}" >> $dot_file

# remove transitivity and produce the png file
tred $dot_file | dot -T png > deps.png

rm $dot_file


