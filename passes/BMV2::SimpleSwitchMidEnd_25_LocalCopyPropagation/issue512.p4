--- dumps/pruned/issue512-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:32.778194500 +0200
+++ dumps/pruned/issue512-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:32.780232300 +0200
@@ -25,29 +25,20 @@ parser parserI(packet_in pkt, out Parsed
     }
 }
 control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
-    bool hasReturned_0;
-    bool cond;
     bool pred;
-    bool cond_0;
-    bool pred_0;
     @name("cIngress.foo") action foo_0() {
-        hasReturned_0 = false;
         meta.b = meta.b + 4w5;
         {
             {
-                cond = meta.b > 4w10;
-                pred = cond;
+                pred = meta.b > 4w10;
                 {
-                    meta.b = (pred ? meta.b ^ 4w5 : meta.b);
-                    hasReturned_0 = (pred ? true : hasReturned_0);
+                    meta.b = (meta.b > 4w10 ? meta.b ^ 4w5 : meta.b);
                 }
             }
         }
         {
             {
-                cond_0 = !hasReturned_0;
-                pred_0 = cond_0;
-                meta.b = (pred_0 ? meta.b + 4w5 : meta.b);
+                meta.b = (!(pred ? true : false) ? meta.b + 4w5 : meta.b);
             }
         }
     }
