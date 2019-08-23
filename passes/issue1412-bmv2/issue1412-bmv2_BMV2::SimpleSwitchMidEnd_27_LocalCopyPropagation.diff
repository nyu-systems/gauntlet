--- before_pass
+++ after_pass
@@ -20,16 +20,12 @@ control IngressImpl(inout headers_t hdr,
     }
 }
 control EgressImpl(inout headers_t hdr, inout metadata meta, inout standard_metadata_t ostd) {
-    bool cond_0;
-    bool pred;
     @name(".NoAction") action NoAction_0() {
     }
     @name("EgressImpl.set_true") action set_true() {
         {
             {
-                cond_0 = meta.field == 8w0;
-                pred = cond_0;
-                meta.cond = (pred ? true : meta.cond);
+                meta.cond = (meta.field == 8w0 ? true : meta.cond);
             }
         }
     }
