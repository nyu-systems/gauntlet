--- before_pass
+++ after_pass
@@ -62,4 +62,4 @@ control c(out bool b) {
 control ce(out bool b);
 parser pe(out bool b);
 package top(pe _p, ce _e, @optional ce _e1);
-top(_e = c(), _p = par()) main;
+top(_p = par(), _e = c()) main;
