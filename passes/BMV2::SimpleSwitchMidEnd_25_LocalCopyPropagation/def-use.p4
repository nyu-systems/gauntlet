--- before_pass
+++ after_pass
@@ -15,7 +15,6 @@ control IngressI(inout H hdr, inout M me
     }
 }
 control EgressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
-    bool hasReturned_0;
     @name("EgressI.a") action a_0() {
     }
     @name("EgressI.t") table t {
@@ -27,10 +26,8 @@ control EgressI(inout H hdr, inout M met
         default_action = a_0();
     }
     apply {
-        hasReturned_0 = false;
         switch (t.apply().action_run) {
             a_0: {
-                hasReturned_0 = true;
             }
             default: {
             }
