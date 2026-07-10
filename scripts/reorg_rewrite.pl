# Reorg import-path rewrite: Fredy.{A#,L#,Deriv*,rel-cluster} -> AOP./leet./rel.
# Idempotent (new names carry no `Fredy.` prefix), lookahead-safe (never touches
# Fredy.S*, Fredy.Locale, Fredy.WellOrdering, the `Fredy.S2_124` namespace, etc.).
# Applied to tracked *.lean and *.md via: git ls-files '*.lean' '*.md' | xargs perl -pi scripts/reorg_rewrite.pl
s/\bFredy\.AutoDerive/rel.AutoDerive/g;
s/\bFredy\.RelInterp/rel.RelInterp/g;
s/\bFredy\.UnixPipe/rel.UnixPipe/g;
s/\bFredy\.ShellCommands/rel.ShellCommands/g;
s/\bFredy\.Deriv1/AOP.Deriv1/g;
s/\bFredy\.DerivMSS/AOP.DerivMSS/g;
s/\bFredy\.A(?=[0-9])/AOP.A/g;
s/\bFredy\.L(?=[0-9])/leet.L/g;
s|\bFredy/AutoDerive|rel/AutoDerive|g;
s|\bFredy/RelInterp|rel/RelInterp|g;
s|\bFredy/UnixPipe|rel/UnixPipe|g;
s|\bFredy/ShellCommands|rel/ShellCommands|g;
s|\bFredy/Deriv1|AOP/Deriv1|g;
s|\bFredy/DerivMSS|AOP/DerivMSS|g;
s|\bFredy/A(?=[0-9])|AOP/A|g;
s|\bFredy/L(?=[0-9])|leet/L|g;
