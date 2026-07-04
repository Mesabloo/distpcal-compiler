import ProgressBar.SpinnerData

-- https://antofthy.gitlab.io/info/ascii/Spinners.txt
-- https://private-user-images.githubusercontent.com/138050/272893742-a3e4d4f9-44c4-4b54-82a7-e608ab1da742.gif?jwt=eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJnaXRodWIuY29tIiwiYXVkIjoicmF3LmdpdGh1YnVzZXJjb250ZW50LmNvbSIsImtleSI6ImtleTUiLCJleHAiOjE3Mzc2NDY3MTMsIm5iZiI6MTczNzY0NjQxMywicGF0aCI6Ii8xMzgwNTAvMjcyODkzNzQyLWEzZTRkNGY5LTQ0YzQtNGI1NC04MmE3LWU2MDhhYjFkYTc0Mi5naWY_WC1BbXotQWxnb3JpdGhtPUFXUzQtSE1BQy1TSEEyNTYmWC1BbXotQ3JlZGVudGlhbD1BS0lBVkNPRFlMU0E1M1BRSzRaQSUyRjIwMjUwMTIzJTJGdXMtZWFzdC0xJTJGczMlMkZhd3M0X3JlcXVlc3QmWC1BbXotRGF0ZT0yMDI1MDEyM1QxNTMzMzNaJlgtQW16LUV4cGlyZXM9MzAwJlgtQW16LVNpZ25hdHVyZT03OGY1YWYwNTllMjg4NzhhNTRmNjBkMDM1ZWJmOTg4OTYxNWJjNDVlMjIyNWQxZGNiMTljMmM3MmJkNDgwMmZmJlgtQW16LVNpZ25lZEhlYWRlcnM9aG9zdCJ9.WQWrIXvuNuLwnbjszgTSaMONr1PFIH-_DyIHSuvbCRI

namespace Spinners
  -- Braille Circling Hole Db
  protected abbrev dots : SpinnerData where
    frames := #["⣶", "⣧", "⣏", "⡟", "⠿", "⢻", "⣹", "⣼"]
    interval := 80

  protected abbrev windowsDots : SpinnerData where
    frames := #[
      "⢀⠀", "⡀⠀", "⠄⠀", "⢂⠀", "⡂⠀", "⠅⠀", "⢃⠀", "⡃⠀", "⠍⠀",
      "⢋⠀", "⡋⠀", "⠍⠁", "⢋⠁", "⡋⠁", "⠍⠉", "⠋⠉", "⠋⠉", "⠉⠙",
      "⠉⠙", "⠉⠩", "⠈⢙", "⠈⡙", "⢈⠩", "⡀⢙", "⠄⡙", "⢂⠩", "⡂⢘",
      "⠅⡘", "⢃⠨", "⡃⢐", "⠍⡐", "⢋⠠", "⡋⢀", "⠍⡁", "⢋⠁", "⡋⠁",
      "⠍⠉", "⠋⠉", "⠋⠉", "⠉⠙", "⠉⠙", "⠉⠩", "⠈⢙", "⠈⡙", "⠈⠩",
      "⠀⢙", "⠀⡙", "⠀⠩", "⠀⢘", "⠀⡘", "⠀⠨", "⠀⢐", "⠀⡐", "⠀⠠",
      "⠀⢀", "⠀⡀"
    ]
    interval := 80

  protected abbrev loadingBar : SpinnerData where
    frames := #[
      "▉ ",
      "🮋▏",
      "🮊▎",
      "🮉▍",
      "▐▌",
      "🮈▋",
      "🮇▊",
      "▕▊",
      " ▉",
      "▏🮋",
      "▎🮊",
      "▍🮉",
      "▌▐",
      "▌🮈",
      "▋🮇",
      "▊▕"
    ]
    interval := 80

  protected abbrev spaceShip : SpinnerData where
    frames := #["➤    ", " ➤   ", "  ➤  ", "   ➤ ", "    ➤"]
    interval := 100

  protected abbrev clock : SpinnerData where
    frames := #["🕛", "🕐", "🕑", "🕒", "🕓", "🕔", "🕕", "🕖", "🕘", "🕙", "🕚"]
    interval := 80

  protected abbrev loadingDots : SpinnerData where
    frames := #["   ", "·  ", "·· ", "···", " ··", "  ·"]
    interval := 150

  protected abbrev sand : SpinnerData where
    frames := #[
      "⠁", "⠂", "⠄", "⡀", "⡈", "⡐", "⡠", "⣀", "⣁", "⣂",
      "⣄", "⣌", "⣔", "⣤", "⣥", "⣦", "⣮", "⣶", "⣷", "⣿",
      "⡿", "⠿", "⢟", "⠟", "⡛", "⠛", "⠫", "⢋", "⠋", "⠍",
      "⡉", "⠉", "⠑", "⠡", "⢁"
    ]
    interval := 80

  protected abbrev dotsCircle : SpinnerData where
    frames := #[
      "  ",
      "⢀ ",
      "⢄ ",
      "⢆ ",
      "⢎ ",
      "⢎⠁",
      "⠎⠑",
      "⠊⠱",
      "⠈⡱",
      "⢀⡱",
      "⢄⡰",
      "⢆⡠",
      "⢎⡀",
      "⢎⠁",
      "⠎⠑",
      "⠊⠱",
      "⠈⡱",
      " ⡱",
      " ⡰",
      " ⡠",
      " ⡀",
      "  "
    ]
    interval := 80
end Spinners
