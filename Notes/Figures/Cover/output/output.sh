inkscape=/Applications/Inkscape.app/Contents/Resources/bin/inkscape
dir=`pwd`
$inkscape -D -z --file="$dir/step1.svg" --export-pdf="$dir/step1.pdf" --export-latex
$inkscape -D -z --file="$dir/step2.svg" --export-pdf="$dir/step2.pdf" --export-latex
$inkscape -D -z --file="$dir/step3.svg" --export-pdf="$dir/step3.pdf" --export-latex
