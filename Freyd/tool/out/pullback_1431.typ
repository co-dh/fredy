#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(width: auto, height: auto, margin: 9mm)
#set text(size: 11pt, font: "New Computer Modern")

#align(center)[#text(13pt, weight: "bold")[The category has pullbacks (§1.431)]]

#align(center)[
#grid(columns: 10, align: horizon, column-gutter: 7mm,
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$forall$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 4), $A$), node((2, 6), $C$), node((4, 4), $B$), edge((0, 4), (2, 6), $a$, "->"), edge((4, 4), (2, 6), $b$, "->")),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$exists$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 4), $A$), node((2, 6), $C$), node((4, 4), $B$), node((0, 2), $P$), edge((0, 4), (2, 6), $a$, "->"), edge((4, 4), (2, 6), $b$, "->"), edge((0, 2), (0, 4), $p$, "->"), edge((0, 2), (4, 4), $q$, "->")),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$forall$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 4), $A$), node((2, 6), $C$), node((4, 4), $B$), node((0, 2), $P$), node((0, 0), $T$), edge((0, 4), (2, 6), $a$, "->"), edge((4, 4), (2, 6), $b$, "->"), edge((0, 2), (0, 4), $p$, "->"), edge((0, 2), (4, 4), $q$, "->"), edge((0, 0), (0, 4), $x$, "->", bend: 22deg), edge((0, 0), (4, 4), $y$, "->", bend: 22deg)),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$exists$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 4), $A$), node((2, 6), $C$), node((4, 4), $B$), node((0, 2), $P$), node((0, 0), $T$), edge((0, 4), (2, 6), $a$, "->"), edge((4, 4), (2, 6), $b$, "->"), edge((0, 2), (0, 4), $p$, "->"), edge((0, 2), (4, 4), $q$, "->"), edge((0, 0), (0, 4), $x$, "->", bend: 22deg), edge((0, 0), (4, 4), $y$, "->", bend: 22deg), edge((0, 0), (0, 2), $m$, "->")),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$!$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 4), $A$), node((2, 6), $C$), node((4, 4), $B$), node((0, 2), $P$), node((0, 0), $T$), edge((0, 4), (2, 6), $a$, "->"), edge((4, 4), (2, 6), $b$, "->"), edge((0, 2), (0, 4), $p$, "->"), edge((0, 2), (4, 4), $q$, "->"), edge((0, 0), (0, 4), $x$, "->", bend: 22deg), edge((0, 0), (4, 4), $y$, "->", bend: 22deg), edge((0, 0), (0, 2), $m$, "->"))
)
]

#align(center)[#text(9pt, style: "italic")[∀ a cospan A→C←B, ∃ P with p:P→A, q:P→B (a p = b q) such that ∀ a cone (x:T→A, y:T→B), ∃ unique m : T→P]]
