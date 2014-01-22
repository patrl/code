<!DOCTYPE HTML>

<html>
<head>
	<title>diptychs</title>
	<meta charset='utf-8'>
	<meta content='width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=0' name='viewport'>
	<link rel="stylesheet" type="text/css" href="css.css">
	<script src="//code.jquery.com/jquery-latest.min.js" type="text/javascript"></script>
	<script src="js.js" type="text/javascript"></script>
</head>

<body>
	<div class="back">
		<div class="arrowleft transitions"></div>
	</div>

	<div class="forward">
		<div class="arrowright transitions"></div>
	</div>

	<div class="container">
		<div class="images transitions"></div>
	</div>

	<div class="thumbs"></div>

	<div class="php"><?php
				$imgloc = 'img';     //put your image directory here
				$ext = 'jpg';                       //if your extension is other than .jpg, you'll need to modify js.js too
    	        //$abspath = realpath($_SERVER["DOCUMENT_ROOT"]);
				$dir = opendir($imgloc);
				while($file = readdir($dir)) {
					if (substr($file, -3) == $ext) {
						print "$file";
					}
				}
				closedir($dir);
    ?></div>
</body>
</html>