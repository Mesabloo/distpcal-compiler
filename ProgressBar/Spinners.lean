module

public import ProgressBar.SpinnerData

public section

-- Spinner frames collected from <https://antofthy.gitlab.io/info/ascii/Spinners.txt>.

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

end
