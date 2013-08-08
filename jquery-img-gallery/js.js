//customize these
var imgs = ["i4", "i5", "i6", "i7", "i8", "i9"];
var imgDir = "../pairs-compressed/";
//end customize
var imgUrls = imgs.map(function(s) {
	return imgDir + s + ".jpg";
});
var makeDivLeft = function(img) {
		return '<div class="showNew" id="' + img + '" style="left:-100%;"><img src="' + imgDir + img + '.jpg" alt="" id="current"></div>';
	};
var makeDivRight = function(img) {
		return '<div class="showNew" id="' + img + '" style="left:100%;"><img src="' + imgDir + img + '.jpg" alt="" id="current"></div>';
	};
var substitute = function(name, toIncrement) {
		var index = imgs.indexOf(name);
		var newIndex = index + toIncrement;
		if (newIndex >= imgs.length) {
			return "i4";
		} else if (newIndex < 0) {
			return "i9";
		} else {
			return imgs[newIndex];
		}
	};
var preLoad = function() { //preload images for nicer transitions
		$(imgUrls).each(function() {
			(new Image()).src = this;
		});
		console.log("preloading imgs...");
	};
var poz = null;
var getPos = function() { //reconstruction as delayed evaluation!
		poz = $(".highlighted").position();
	};
var goBack = function() {
		var oldImg = $(".show").attr("id");
		var newImg = substitute(oldImg, -1);
		var newDiv = makeDivLeft(newImg);
		$(".show").animate({
			left: "100%",
			opacity: "0"
		}, 250, function() {
    		$(this).remove();
		});
		$(".container").append(newDiv);
		$(".showNew").animate({
			left: "0",
			opacity: "1"
		}, 250, function() {
    		$(this).toggleClass("showNew").toggleClass("show");
		});
		$("#" + oldImg + "small, #" + newImg + "small").toggleClass("highlighted");
		getPos();
		$(".slider").animate({
			left: String(poz.left + 2)
		}, 500);
	};
var goForward = function() {
		var oldImg = $(".show").attr("id");
		var newImg = substitute(oldImg, 1);
		var newDiv = makeDivRight(newImg);
		$(".show").animate({
			left: "-100%",
			opacity: "0"
		}, 250, function() {
    		$(this).remove();
		});
		$(".container").append(newDiv);
		$(".showNew").animate({
			left: "0",
			opacity: "1"
		}, 250, function() {
    		$(this).toggleClass("showNew").toggleClass("show");
		});
		$("#" + oldImg + "small, #" + newImg + "small").toggleClass("highlighted");
		getPos();
		$(".slider").animate({
			left: String(poz.left + 2)
		}, 500);
	};
$(function() { //on document ready:::
	$(window).load(function() { //preload images after, hide navigation until, main image loads
    	preLoad();
    	$(".thumbs").animate({
        	opacity: "1"
    	}, 200);
	});
	getPos();
	$(".slider").css({ //set initial slider position
		"left": poz.left + 2
	});
	var img = $('#current');
	if (img.prop('complete')) { //set initial heights of container, click-divs; set nav arrow position
		var initHeight = $("#current").height();
		$(".container,.show").css({
			"min-height": initHeight
		});
		$(".back,.forward").css({
			"height": initHeight
		});
		$(".arrowleft,.arrowright").css({
			"top": initHeight / 2 - 10
		});
	} else {
		img.load(function() {
			var initHeight = $("#current").height();
			$(".container").css({
				"min-height": initHeight
			});
			$(".back,.forward").css({
				"height": initHeight
			});
			$(".arrowleft,.arrowright").css({
				"top": initHeight / 2 - 10
			});
		});
	}
	$(window).resize(function() { //slider, container, click-divs shift w/resize
		poz = $(".highlighted").position();
		$(".slider").css({
			"left": poz.left + 2
		});
		var imgHeight = $("#current").height();
		$(".container").css({
			"min-height": imgHeight
		});
		$(".back,.forward").css({
			"height": imgHeight
		});
		$(".arrowleft,.arrowright").css({
			"top": imgHeight / 2 - 10
		});
	});
	$(".fadeIn").animate({
		opacity: "1"
	}, 200);
	var lastClick = 0;
	$(".back").click( //back click behavior
    	function(event) {
    		var newClick = event.timeStamp;
    		var interval = newClick - lastClick;
    		if (interval > 500) { //wait for 500ms animations to finish, on pain of screwing up slider
    			goBack();
    			lastClick = newClick;
    		}
	}).hover( //back nav arrow sliding
    	function() {
    		$(".arrowleft").animate({
    			left: "+=50"
    		}, 500);
    	}, function() {
    		$(".arrowleft").animate({
    			left: "-=50"
    		}, 500);
	});
	$(".forward").click( //forward click behavior
    	function(event) {
    		var newClick = event.timeStamp;
    		var interval = newClick - lastClick;
    		if (interval > 500) { //wait for 500ms animations to finish, on pain of screwing up slider
    			goForward();
    			lastClick = newClick;
    		}
	}).hover(
    	function() {
    		$(".arrowright").animate({
    			right: "+=50"
    		}, 500);
    	}, function() {
    		$(".arrowright").animate({
    			right: "-=50"
    		}, 500);
	});
	var lastPress = 0;
	var interval = 0;
	$(document.documentElement).keyup(function(event) { //keyboard navigation
		var k = event.keyCode;
		newPress = event.timeStamp;
		interval = newPress - lastPress;
		if (k == 37 && interval > 500) { //wait for 500ms animations to finish, on pain of screwing up slider
			goBack();
			lastPress = newPress;
		} else if (k == 39 && interval > 500) {
			goForward();
			lastPress = newPress;
		}
	}).keydown(function(event) { //firefox arrowkey navigation bug fix
		var k = event.keyCode;
		if (k >= 37 && k <= 40) {
			return false;
		}
	});
});