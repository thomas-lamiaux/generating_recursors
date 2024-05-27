COQDEP_OPTS="-R . GenRecursor recursors_named/*.v"  # your -Q and -R options, and the filenames
# Usage:
#
#    # Step 0. Edit COQDEP_OPTS above to match your _CoqProject
#
#    # Step 1. Use this script to generate the dependency graph
#    sh dotdeps.sh
#
#    # Output in file deps.jpg
#
(echo "digraph interval_deps {" ;
echo "node [shape=ellipse, style=filled, URL=\"\N.svg\", color=black];";
coqdep $COQDEP_OPTS | sed -e 's,recursors_named/,,g' | sed -n -e 's,/,.,g;s/[.]vo.*: [^ ]*[.]v//p' |
while read src dst; do
    color="pink"
    echo "\"$src\" [fillcolor=$color];"
    for d in $dst; do
    echo "\"${d%.vo}\" -> \"$src\" ;"
    # echo "\"$src\" -> \"${d%.vo}\" ;"
    done
done;
echo "}") | tred > deps.dot
dot deps.dot -Tjpg -o deps.jpg
