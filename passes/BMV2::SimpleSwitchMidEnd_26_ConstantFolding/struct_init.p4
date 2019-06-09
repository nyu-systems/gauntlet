--- before_pass
+++ after_pass
@@ -6,7 +6,7 @@ struct metadata_t {
 }
 control I(inout metadata_t meta) {
     apply {
-        if (true && meta._foo__v0 == 9w192) 
+        if (meta._foo__v0 == 9w192) 
             meta._foo__v0 = meta._foo__v0 + 9w1;
     }
 }
