--- before_pass
+++ after_pass
@@ -5,7 +5,7 @@ control c(out bool b) {
     emptyTuple t_0;
     apply {
         t_0 = {  };
-        if (t_0 == {  }) 
+        if (true) 
             b = true;
         else 
             b = false;
