$(function() {
	//begin customize
	imgDir = "img/";
	scaleFactor = 1;
	sliderOffset = 2;
	//end customize
	imgs = $(".php").html().split(".jpg").filter(function(i) {
		return i !== "";
	}).sort();
	imgUrls = imgs.map(function(s) {
		return imgDir + s + ".jpg";
	});
	thumbUrls = imgs.map(function(s) {
		return imgDir + 'thumbs/' + s + ".jpg";
	});
	for (i = 0; i < imgs.length; i++) {
		if (i === 0) {
			$(".images").append('<img src="' + imgUrls[i] + '" class="big first" id="' + imgs[i] + '" alt="">');
		} else {
			$(".images").append('<img class="big hidden" id="' + imgs[i] + '" src="" alt="">');
		}
	}
	for (i = 0; i < imgs.length; i++) {
		if (i === 0) {
			$(".thumbs").append('<img src="' + thumbUrls[i] + '" id="' + imgs[i] + 'small' + '" class="highlighted" alt="">');
		} else {
			$(".thumbs").append('<img src="' + thumbUrls[i] + '" id="' + imgs[i] + 'small' + '" alt="">');
		}
	}
	$(".thumbs").append('<div class="slider transitions"></div>');
	setWidths = function() {
		bodyWidth = $("body").width() * scaleFactor;
		$(".container img,.container").css({
			"width": bodyWidth
		});
		$(".images").css({
			"width": imgs.length * bodyWidth
		});
	};
	setHeights = function() {
		var imgHeight = $(".first").height();
		$(".back,.forward,.container,.images").css({
			"height": imgHeight
		});
		$(".arrowleft,.arrowright").css({
			"top": imgHeight / 2 - 10
		});
	};
	setSlider = function() {
		var poz = $(".highlighted").position();
		$(".slider").css({
			"left": poz.left + sliderOffset
		});
	};
	goTo = function(nextImage) {
		$(".highlighted").toggleClass("highlighted");
		nextImage.addClass("highlighted");
		$(".images").css("transform", "translateX(" + nextImage.index() * -bodyWidth + "px)");
		var toLoad = $("#" + nextImage.attr('id').slice(0, -5));
		clearInterval(intervalId); //cancel the last-triggered loop
		if (toLoad.prop('complete') && toLoad.attr('src') !== '') {
			setSlider();
		} else {
			moveSlider();
			var param = setInterval(moveSlider, 1000);
			intervalId = param;
			toLoad.load(function() {
				if (toLoad.attr('id') === $('.highlighted').attr('id').slice(0, -5)) { //fix setslider bug
    				clearInterval(param);
    				clearTimeout(timeoutId);
					setSlider();
				}
			});
		}
	};
	preLoad = function() {
		for (var i = 1; i < imgs.length; i++) {
			$("#" + imgs[i]).attr('src', imgUrls[i]);
			nth = i + 1;
			console.log('...preloading image #' + nth + '...');
			if (i === imgs.length - 1) {
				$(".hidden").fadeIn();
			}
		}
	};
	sliderWidth = $(".slider").width();
	howFar = $("body").width() - sliderWidth;
	moveSlider = function() {
		$(".slider").css({
			"left": howFar
		});
		timeoutId = setTimeout(function() {
			$(".slider").css({
				"left": 0
			});
		}, 500);
	};
	moveSlider();
	var param = setInterval(moveSlider, 1000);
	intervalId = param;
	$(window).load(function() {
		console.log("Main image loaded, preloading rest of images...");
		preLoad();
		setHeights();
		if ($('.first').attr('id') === $('.highlighted').attr('id').slice(0, -5)) { //unift with above
    		clearInterval(param);
    		clearTimeout(timeoutId);
			setSlider();
		}
	});
	setWidths();
	$(".thumbs img").click(function() {
		goTo($(this));
	}).bind('touchstart', function() { //iOS
		$(this).css({
			"opacity": 1
		}).siblings().css({
			"opacity": 0.5
		});
	});
	$(".back,.forward").bind('touchstart', function() { //more iOS
		$(".thumbs img").css({
			"opacity": 0.5
		});
	});
	$(".back").click(function() {
		if ($(".highlighted").index() > 0) {
			goTo($(".highlighted").prev());
		}
	});
	$(".forward").click(function() {
		if ($(".highlighted").index() < imgs.length - 1) {
			goTo($(".highlighted").next());
		}
	});
	$(document.documentElement).keydown(function(event) { //keyboard navigation
		var k = event.keyCode;
		if (k == 37 && $(".highlighted").index() > 0) {
			goTo($(".highlighted").prev());
		} else if (k == 39 && $(".highlighted").index() < imgs.length - 1) {
			goTo($(".highlighted").next());
		}
		if (k >= 37 && k <= 40) {
			return false;
		}
	});
	$(window).resize(function() {
		setWidths(); //important to set widths before heights
		setHeights();
		$(".images,.slider").removeClass("transitions");
		setSlider();
		setTimeout(function() {
			$(".images,.slider").addClass("transitions");
		}, 5);
		$(".images").css("transform", "translateX(" + $(".highlighted").index() * -bodyWidth + "px)");
	});
	$('img').on('dragstart', function(e) {
		e.preventDefault();
	}); //no accidentally dragging images
});