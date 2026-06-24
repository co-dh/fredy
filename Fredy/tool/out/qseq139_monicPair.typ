#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(width: auto, height: auto, margin: 9mm)
#set text(size: 11pt, font: "New Computer Modern")

#align(center)[#text(13pt, weight: "bold")[⟨x,y⟩ monic — §1.41 monic-pair (puncture) Q-sequence]]

#align(center)[
#grid(columns: 5, align: horizon, column-gutter: 6mm,
  diagram(spacing: (12mm, 11mm), node-stroke: none, node((0, 2), $T$), node((0, 4), $A times B$), node((0, 6), $A$), node((4, 6), $B$), edge((0, 2), (0, 4), $m$, "->"), edge((0, 4), (0, 6), $l$, "->"), edge((0, 4), (4, 6), $r$, "->"), edge((0, 2), (0, 6), $x$, "->", bend: 24deg), edge((0, 2), (4, 6), $y$, "->", bend: 24deg)),
  box(height: 40mm)[#stack(dir: ttb, spacing: 3mm, align(center)[#text(13pt)[$forall$]], line(length: 32mm, angle: 90deg))],
  diagram(spacing: (12mm, 11mm), node-stroke: none, node((0, 2), $T$), node((0, 4), $A times B$), node((0, 6), $A$), node((4, 6), $B$), node((0, 0), $W$), edge((0, 2), (0, 4), $m$, "->"), edge((0, 4), (0, 6), $l$, "->"), edge((0, 4), (4, 6), $r$, "->"), edge((0, 2), (0, 6), $x$, "->", bend: 24deg), edge((0, 2), (4, 6), $y$, "->", bend: 24deg), edge((0, 0), (0, 2), $a$, "->", shift: 6pt, label-side: left), edge((0, 0), (0, 2), $b$, "->", shift: -6pt, label-side: right), node(((0+0)/2, (0+2)/2), text(13pt)[$plus$])),
  box(height: 40mm)[#stack(dir: ttb, spacing: 3mm, align(center)[#text(13pt)[$exists$]], line(length: 32mm, angle: 90deg))],
  diagram(spacing: (12mm, 11mm), node-stroke: none, node((0, 2), $T$), node((0, 4), $A times B$), node((0, 6), $A$), node((4, 6), $B$), node((0, 0), $W$), edge((0, 2), (0, 4), $m$, "->"), edge((0, 4), (0, 6), $l$, "->"), edge((0, 4), (4, 6), $r$, "->"), edge((0, 2), (0, 6), $x$, "->", bend: 24deg), edge((0, 2), (4, 6), $y$, "->", bend: 24deg), edge((0, 0), (0, 2), $a$, "->", shift: 6pt, label-side: left), edge((0, 0), (0, 2), $b$, "->", shift: -6pt, label-side: right))
)
]
