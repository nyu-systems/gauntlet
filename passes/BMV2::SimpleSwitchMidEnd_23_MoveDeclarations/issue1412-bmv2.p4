--- dumps/p4_16_samples/issue1412-bmv2.p4/pruned/issue1412-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 17:30:15.646368200 +0200
+++ dumps/p4_16_samples/issue1412-bmv2.p4/pruned/issue1412-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:30:15.648985300 +0200
@@ -20,13 +20,13 @@ control IngressImpl(inout headers_t hdr,
     }
 }
 control EgressImpl(inout headers_t hdr, inout metadata meta, inout standard_metadata_t ostd) {
+    bool cond_0;
+    bool pred;
     @name(".NoAction") action NoAction_0() {
     }
     @name("EgressImpl.set_true") action set_true_0() {
         {
-            bool cond_0;
             {
-                bool pred;
                 cond_0 = meta.field == 8w0;
                 pred = cond_0;
                 meta.cond = (pred ? true : meta.cond);
