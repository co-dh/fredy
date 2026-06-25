#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(width: auto, height: auto, margin: 9mm)
#set text(size: 11pt, font: "New Computer Modern")

#align(center)[#text(13pt, weight: "bold")[P is PROJECTIVE (§1.524)]]

#align(center)[
#grid(columns: 5, align: horizon, column-gutter: 7mm,
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((1, 0), $P$)),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$forall$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((2, 0), $P$), node((0, 2), $A$), node((2, 2), $B$), edge((0, 2), (2, 2), "->>"), edge((2, 0), (2, 2), "->")),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$exists$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((2, 0), $P$), node((0, 2), $A$), node((2, 2), $B$), edge((2, 0), (0, 2), "->"), edge((0, 2), (2, 2), "->>"), edge((2, 0), (2, 2), "->"))
)
]

#align(center)[#text(9pt, style: "italic")[∀ cover A↠B and P→B, ∃ a lift P→A]]
