#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(width: auto, height: auto, margin: 9mm)
#set text(size: 11pt, font: "New Computer Modern")

#align(center)[#text(13pt, weight: "bold")[Empty union: the minimal subobject (§1.611)]]

#align(center)[
#grid(columns: 6, align: horizon, column-gutter: 7mm,
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$exists$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 2), $A$)),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$forall$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 2), $A$), node((0, 0), $B$), edge((0, 0), (0, 2), "->", shift: 6pt, label-side: left)),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$exists$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 2), $A$), node((0, 0), $B$), edge((0, 0), (0, 2), "->", shift: 6pt, label-side: left), edge((0, 2), (0, 0), "->", shift: -6pt, label-side: right))
)
]

#align(center)[#text(9pt, style: "italic")[∃ A, ∀ (f : B → A), ∃ (g : A → B) inverse to f — every map to A is iso (A = the least subobject)]]
