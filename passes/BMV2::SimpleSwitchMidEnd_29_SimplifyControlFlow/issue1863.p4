--- before_pass
+++ after_pass
@@ -4,10 +4,6 @@ struct S {
 }
 control c(out bit<1> b) {
     apply {
-        {
-        }
-        {
-        }
         b = 1w1;
     }
 }
