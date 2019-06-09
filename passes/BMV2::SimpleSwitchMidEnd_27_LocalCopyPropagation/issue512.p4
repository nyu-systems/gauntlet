--- before_pass
+++ after_pass
@@ -25,29 +25,20 @@ parser parserI(packet_in pkt, out Parsed
     }
 }
 control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
-    bool hasReturned;
-    bool cond;
     bool pred;
-    bool cond_0;
-    bool pred_0;
     @name("cIngress.foo") action foo() {
-        hasReturned = false;
         meta.b = meta.b + 4w5;
         {
             {
-                cond = meta.b > 4w10;
-                pred = cond;
+                pred = meta.b > 4w10;
                 {
-                    meta.b = (pred ? meta.b ^ 4w5 : meta.b);
-                    hasReturned = (pred ? true : hasReturned);
+                    meta.b = (meta.b > 4w10 ? meta.b ^ 4w5 : meta.b);
                 }
             }
         }
         {
             {
-                cond_0 = !hasReturned;
-                pred_0 = cond_0;
-                meta.b = (pred_0 ? meta.b + 4w5 : meta.b);
+                meta.b = (!(pred ? true : false) ? meta.b + 4w5 : meta.b);
             }
         }
     }
