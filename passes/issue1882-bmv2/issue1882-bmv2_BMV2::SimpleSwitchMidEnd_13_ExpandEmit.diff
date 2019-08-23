--- before_pass
+++ after_pass
@@ -25,7 +25,8 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        b.emit<Headers>(h);
+        {
+        }
     }
 }
 extern ExternCounter {
