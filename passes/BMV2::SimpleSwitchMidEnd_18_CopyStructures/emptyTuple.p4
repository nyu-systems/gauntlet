--- before_pass
+++ after_pass
@@ -4,7 +4,8 @@ typedef tuple_0 emptyTuple;
 control c(out bool b) {
     emptyTuple t_0;
     apply {
-        t_0 = {  };
+        {
+        }
         if (true) 
             b = true;
         else 
