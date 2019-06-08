--- dumps/pruned/struct_init-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:34:06.703451100 +0200
+++ dumps/pruned/struct_init-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:34:06.707272200 +0200
@@ -6,7 +6,7 @@ struct metadata_t {
 }
 control I(inout metadata_t meta) {
     apply {
-        if (true && meta.foo._v == 9w192) 
+        if (meta.foo._v == 9w192) 
             meta.foo._v = meta.foo._v + 9w1;
     }
 }
