#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(width: auto, height: auto, margin: 9mm)
#set text(size: 11pt, font: "New Computer Modern")

#align(center)[#text(13pt, weight: "bold")[Left-invertible (§1.39)]]

#align(center)[
#grid(columns: 3, align: horizon, column-gutter: 7mm,
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 0), $A$), node((0, 2), $B$), edge((0, 0), (0, 2), $f$, "->", shift: 6pt, label-side: left)),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$exists$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 0), $A$), node((0, 2), $B$), edge((0, 0), (0, 2), $f$, "->", shift: 6pt, label-side: left), edge((0, 2), (0, 0), $g$, "->", shift: -6pt, label-side: right))
)
]

#align(center)[#text(9pt, style: "italic")[given f : A → B, ∃ g : B → A with f g = 1_A]]
