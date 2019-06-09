--- before_pass
+++ after_pass
@@ -15,6 +15,7 @@ control IngressI(inout H hdr, inout M me
     }
 }
 control EgressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
+    bool hasReturned;
     @name("EgressI.a") action a() {
     }
     @name("EgressI.t") table t_0 {
@@ -26,7 +27,7 @@ control EgressI(inout H hdr, inout M met
         default_action = a();
     }
     apply {
-        bool hasReturned = false;
+        hasReturned = false;
         switch (t_0.apply().action_run) {
             a: {
                 hasReturned = true;
