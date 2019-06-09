--- before_pass
+++ after_pass
@@ -9,7 +9,7 @@ struct test_struct {
     error test_error;
 }
 struct local_metadata_t {
-    test_struct test;
+    error _test_test_error0;
 }
 parser parse(packet_in pk, out parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
     state start {
@@ -18,7 +18,7 @@ parser parse(packet_in pk, out parsed_pa
 }
 control ingress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
     apply {
-        if (local_metadata.test.test_error == error.Unused) 
+        if (local_metadata._test_test_error0 == error.Unused) 
             mark_to_drop(standard_metadata);
     }
 }
