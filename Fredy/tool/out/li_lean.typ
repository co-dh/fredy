#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(width: auto, height: auto, margin: 9mm)
#set text(size: 11pt, font: "New Computer Modern")

#align(center)[#text(13pt, weight: "bold")[Left-invertible (§1.39)]]

#align(center)[
#grid(columns: 3, align: horizon, column-gutter: 7mm,
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 1), $A$), node((1, 1), $B$), edge((0, 1), (1, 1), $f$, "->")),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$exists$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 0), $B$), node((0, 1), $A$), node((1, 1), $B$), edge((0, 0), (0, 1), $g$, "->"), edge((0, 1), (1, 1), $f$, "->"), edge((0, 0), (1, 1), $1$, "->"))
)
]

#align(center)[#text(9pt, style: "italic")[∃ the back-arrow making the triangle commute (g; f = 1)]]
