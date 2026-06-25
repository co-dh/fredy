#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(width: auto, height: auto, margin: 9mm)
#set text(size: 11pt, font: "New Computer Modern")

#align(center)[#text(13pt, weight: "bold")[Binary union of two subobjects (§1.611)]]

#align(center)[
#grid(columns: 4, align: horizon, column-gutter: 7mm,
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$forall$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 0), $B_1$), node((4, 0), $B_2$), node((2, 4), $B$), edge((0, 0), (2, 4), ">->", bend: 22deg), edge((4, 0), (2, 4), ">->", bend: -22deg)),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$exists$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 0), $B_1$), node((4, 0), $B_2$), node((2, 4), $B$), node((2, 2), $U$), edge((0, 0), (2, 4), ">->", bend: 22deg), edge((4, 0), (2, 4), ">->", bend: -22deg), edge((0, 0), (2, 2), "->"), edge((4, 0), (2, 2), "->"), edge((2, 2), (2, 4), ">->"), edge((1, 1), (3, 1), "-", bend: 35deg))
)
]

#align(center)[#text(9pt, style: "italic")[∀ subobjects B₁, B₂ ↣ B, ∃ U = B₁∪B₂ with B₁, B₂ JOINTLY covering U and U ↣ B monic]]
