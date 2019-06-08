--- dumps/pruned/issue1412-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:01.384361100 +0200
+++ dumps/pruned/issue1412-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:01.386415800 +0200
@@ -20,16 +20,12 @@ control IngressImpl(inout headers_t hdr,
     }
 }
 control EgressImpl(inout headers_t hdr, inout metadata meta, inout standard_metadata_t ostd) {
-    bool cond_0;
-    bool pred;
     @name(".NoAction") action NoAction_0() {
     }
     @name("EgressImpl.set_true") action set_true_0() {
         {
             {
-                cond_0 = meta.field == 8w0;
-                pred = cond_0;
-                meta.cond = (pred ? true : meta.cond);
+                meta.cond = (meta.field == 8w0 ? true : meta.cond);
             }
         }
     }
