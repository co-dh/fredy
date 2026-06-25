#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(width: auto, height: auto, margin: 9mm)
#set text(size: 11pt, font: "New Computer Modern")

#align(center)[#text(13pt, weight: "bold")[Pullbacks transfer finite covers (§1.611)]]

#align(center)[
#grid(columns: 4, align: horizon, column-gutter: 7mm,
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$forall$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((2, 2), $A$), node((0, 2), $B_1$), node((2, 4), $B$), node((4, 2), $B_2$), edge((2, 2), (2, 4), "->"), edge((0, 2), (2, 4), "->"), edge((4, 2), (2, 4), "->"), edge((1, 3), (3, 3), "-", bend: -35deg)),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$exists$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((2, 2), $A$), node((0, 2), $B_1$), node((2, 4), $B$), node((4, 2), $B_2$), node((0, 0), $A_1$), node((4, 0), $A_2$), edge((2, 2), (2, 4), "->"), edge((0, 2), (2, 4), "->"), edge((4, 2), (2, 4), "->"), edge((0, 0), (2, 2), "->"), edge((4, 0), (2, 2), "->"), edge((0, 0), (0, 2), "->"), edge((4, 0), (4, 2), "->"), edge((1, 3), (3, 3), "-", bend: -35deg), edge((1, 1), (3, 1), "-", bend: 35deg))
)
]

#align(center)[#text(9pt, style: "italic")[∀ a cover {B₁, B₂} of B (jointly) and a map A → B, ∃ pullbacks {A₁, A₂} jointly covering A]]
