#!/usr/bin/env perl
# Rewrite the coqdoc comments in a .v file so pages render cleanly.
#
#   1) Strip the Javadoc-style leading " * " inside (** ... *) doc comments.
#      coqdoc reads a line beginning with '*' as a SECTION HEADING marker,
#      so Javadoc continuation lines explode one paragraph into a stack of
#      giant <h1>s.  Removing the leading star makes them ordinary prose.
#
#   2) Turn the three-line banner comments
#          (* ============ *)
#          (* Title        *)
#          (* ============ *)
#      into a coqdoc heading  (** * Title *)  — a real section heading that
#      also feeds the per-page table of contents.
#
# Comments do not affect compilation, so this is proof-safe; `make` after
# running it will catch any accidental structural breakage.
#
# Usage:  perl scripts/clean-doc-comments.pl FILE.v [FILE.v ...]

use strict;
use warnings;

for my $file (@ARGV) {
  local $/;
  open my $fh, '<', $file or die "$file: $!";
  my $s = <$fh>;
  close $fh;

  # (1) leading " * " inside (** ... *) blocks.  The lookbehind for a
  #     newline means we only strip continuation-line stars, never a
  #     heading marker like "(** * Title *)" (whose star follows "(**",
  #     not a newline) — so this transform is idempotent.
  $s =~ s{\(\*\*(.*?)\*\)}{
    my $b = $1;
    $b =~ s/(?<=\n)[ \t]?\*[ \t]?//g;
    "(**$b*)"
  }ges;

  # (2) banner triples -> coqdoc headings
  $s =~ s{
    ^[ \t]*\(\*[ \t]=+[ \t]\*\)[ \t]*\n
    [ \t]*\(\*[ \t](.+?)[ \t]*\*\)[ \t]*\n
    [ \t]*\(\*[ \t]=+[ \t]\*\)[ \t]*
  }{
    my $t = $1;
    $t =~ s/\s+$//;
    "(** * $t *)"
  }gemx;

  open my $out, '>', $file or die "$file: $!";
  print $out $s;
  close $out;
}
