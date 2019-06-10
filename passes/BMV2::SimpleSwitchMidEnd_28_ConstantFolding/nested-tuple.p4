--- before_pass
+++ after_pass
@@ -31,7 +31,7 @@ control c(inout bit<1> r) {
         }
         f<tuple_1>({ s_0_f1_field, s_0_f1_field_0 });
         f<tuple_0>(tuple_0 {field = T {f = 1w0},field_0 = T {f = 1w1}});
-        r = 1w0 & 1w1;
+        r = 1w0;
     }
 }
 control simple(inout bit<1> r);
