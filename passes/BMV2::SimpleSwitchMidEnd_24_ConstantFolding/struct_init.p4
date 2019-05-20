--- dumps/p4_16_samples/struct_init.p4/pruned/struct_init-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:32:17.618255300 +0200
+++ dumps/p4_16_samples/struct_init.p4/pruned/struct_init-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:32:17.620814500 +0200
@@ -6,7 +6,7 @@ struct metadata_t {
 }
 control I(inout metadata_t meta) {
     apply {
-        if (true && meta.foo._v == 9w192) 
+        if (meta.foo._v == 9w192) 
             meta.foo._v = meta.foo._v + 9w1;
     }
 }
