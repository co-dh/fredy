#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(width: auto, height: auto, margin: 9mm)
#set text(size: 11pt, font: "New Computer Modern")

#align(center)[#text(13pt, weight: "bold")[A is a sub-terminator (§1.412)]]

#align(center)[
#grid(columns: 5, align: horizon, column-gutter: 7mm,
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 2), $A$)),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$forall$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 2), $A$), node((0, 0), $X$)),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$!$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 2), $A$), node((0, 0), $X$), edge((0, 0), (0, 2), $h$, "->"))
)
]

#align(center)[#text(9pt, style: "italic")[∀ X, ! (at most one) map X → A]]
