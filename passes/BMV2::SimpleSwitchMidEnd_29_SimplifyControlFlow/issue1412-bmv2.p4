--- before_pass
+++ after_pass
@@ -23,11 +23,7 @@ control EgressImpl(inout headers_t hdr,
     @name(".NoAction") action NoAction_0() {
     }
     @name("EgressImpl.set_true") action set_true_0() {
-        {
-            {
-                meta.cond = (meta.field == 8w0 ? true : meta.cond);
-            }
-        }
+        meta.cond = (meta.field == 8w0 ? true : meta.cond);
     }
     @name("EgressImpl.change_cond") table change_cond {
         key = {
