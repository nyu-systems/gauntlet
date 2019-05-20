--- dumps/p4_16_samples/issue696-bmv2.p4/pruned/issue696-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:31:02.989960600 +0200
+++ dumps/p4_16_samples/issue696-bmv2.p4/pruned/issue696-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:31:02.998426200 +0200
@@ -51,38 +51,24 @@ control Ing(inout Headers headers, inout
 }
 control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
     Value val;
-    bool _pred;
     bit<32> inc;
     bit<32> tmp_1;
     bit<32> tmp_2;
-    bool cond;
-    bool pred;
-    bool cond_0;
-    bool pred_0;
     @name("Eg.test") action test_0() {
         {
             val.field1 = 32w0;
         }
-        _pred = val.field1 != 32w0;
         {
             {
-                cond = _pred;
-                pred = cond;
-                tmp_1 = (pred ? 32w1 : tmp_1);
-                cond = !cond;
-                pred = cond;
-                tmp_1 = (pred ? 32w0 : tmp_1);
+                tmp_1 = (32w0 != 32w0 ? 32w1 : tmp_1);
+                tmp_1 = (!(32w0 != 32w0) ? 32w0 : tmp_1);
             }
         }
         inc = tmp_1;
         {
             {
-                cond_0 = _pred;
-                pred_0 = cond_0;
-                tmp_2 = (pred_0 ? 32w1 : tmp_2);
-                cond_0 = !cond_0;
-                pred_0 = cond_0;
-                tmp_2 = (pred_0 ? 32w0 : tmp_2);
+                tmp_2 = (32w0 != 32w0 ? 32w1 : tmp_2);
+                tmp_2 = (!(32w0 != 32w0) ? 32w0 : tmp_2);
             }
         }
         debug.write(32w0, tmp_2);
