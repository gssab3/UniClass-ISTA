package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.service.AnnoDidatticoService;
import it.unisa.uniclass.orari.service.dao.AnnoDidatticoRemote;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@DisplayName("Test per la classe AnnoDidatticoService")
public class AnnoDidatticoServiceTest {

    @Mock
    private AnnoDidatticoRemote annoDidatticoDao;

    private AnnoDidatticoService annoDidatticoService;
    private AnnoDidattico annoDidattico;

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);

        annoDidatticoService = new AnnoDidatticoService(annoDidatticoDao);

        annoDidattico = new AnnoDidattico("2023-2024");
        annoDidattico.setCorsiLaurea(new ArrayList<>());
        annoDidattico.setCorsi(new ArrayList<>());
    }

    @Nested
    @DisplayName("Test dei costruttori")
    class CostruttoriTest {

        @Test
        @DisplayName("Costruttore con parametro inietta correttamente il DAO")
        void testCostruttoreConParametro() {
            AnnoDidatticoRemote mockDao = mock(AnnoDidatticoRemote.class);
            AnnoDidatticoService service = new AnnoDidatticoService(mockDao);
            assertNotNull(service);
        }

        @Test
        @DisplayName("Costruttore senza parametri crea comunque l'istanza")
        void testCostruttoreVuoto() {
            AnnoDidatticoService service = new AnnoDidatticoService();
            assertNotNull(service);
        }
    }

    @Nested
    @DisplayName("Test trovaAnno")
    class TrovaAnnoTest {

        @Test
        void testSuccesso() {
            when(annoDidatticoDao.trovaAnno("2023-2024"))
                    .thenReturn(List.of(annoDidattico));

            List<AnnoDidattico> result = annoDidatticoService.trovaAnno("2023-2024");

            assertEquals(1, result.size());
        }

        @Test
        void testVuoto() {
            when(annoDidatticoDao.trovaAnno("2099-2100"))
                    .thenReturn(new ArrayList<>());

            assertTrue(annoDidatticoService.trovaAnno("2099-2100").isEmpty());
        }
    }

    @Nested
    @DisplayName("Test trovaId")
    class TrovaIdTest {

        @Test
        void testSuccesso() {
            when(annoDidatticoDao.trovaId(1)).thenReturn(annoDidattico);

            AnnoDidattico result = annoDidatticoService.trovaId(1);

            assertNotNull(result);
        }

        @Test
        void testNonTrovato() {
            when(annoDidatticoDao.trovaId(999)).thenThrow(new NoResultException());

            assertNull(annoDidatticoService.trovaId(999));
        }
    }

    @Nested
    @DisplayName("Test trovaTutti")
    class TrovaTuttiTest {

        @Test
        void testSuccesso() {
            when(annoDidatticoDao.trovaTutti()).thenReturn(List.of(annoDidattico));
            assertEquals(1, annoDidatticoService.trovaTutti().size());
        }

        @Test
        void testVuoto() {
            when(annoDidatticoDao.trovaTutti()).thenReturn(new ArrayList<>());
            assertTrue(annoDidatticoService.trovaTutti().isEmpty());
        }
    }

    @Nested
    @DisplayName("Test aggiungiAnno")
    class AggiungiAnnoTest {

        @Test
        void testSuccesso() {
            annoDidatticoService.aggiungiAnno(annoDidattico);
            verify(annoDidatticoDao).aggiungiAnno(annoDidattico);
        }
    }

    @Nested
    @DisplayName("Test rimuoviAnno")
    class RimuoviAnnoTest {

        @Test
        void testSuccesso() {
            annoDidatticoService.rimuoviAnno(annoDidattico);
            verify(annoDidatticoDao).rimuoviAnno(annoDidattico);
        }
    }

    @Nested
    @DisplayName("Test trovaTuttiCorsoLaurea")
    class TrovaTuttiCorsoLaureaTest {

        @Test
        void testSuccesso() {
            when(annoDidatticoDao.trovaTuttiCorsoLaurea(1L))
                    .thenReturn(List.of(annoDidattico));

            assertEquals(1, annoDidatticoService.trovaTuttiCorsoLaurea(1L).size());
        }
    }

    @Nested
    @DisplayName("Test trovaTuttiCorsoLaureaNome")
    class TrovaTuttiCorsoLaureaNomeTest {

        @Test
        void testSuccesso() {
            when(annoDidatticoDao.trovaCorsoLaureaNome(1L, "2023-2024"))
                    .thenReturn(annoDidattico);

            AnnoDidattico result = annoDidatticoService.trovaTuttiCorsoLaureaNome(1L, "2023-2024");

            assertNotNull(result);
        }

        @Test
        void testNonTrovato() {
            when(annoDidatticoDao.trovaCorsoLaureaNome(1L, "X"))
                    .thenThrow(new NoResultException());

            assertNull(annoDidatticoService.trovaTuttiCorsoLaureaNome(1L, "X"));
        }
    }

    @Nested
    @DisplayName("Test integrazione")
    class ScenariComplessiTest {

        @Test
        void testSequenzaCompleta() {
            annoDidatticoService.aggiungiAnno(annoDidattico);
            verify(annoDidatticoDao).aggiungiAnno(annoDidattico);

            when(annoDidatticoDao.trovaId(1)).thenReturn(annoDidattico);
            assertNotNull(annoDidatticoService.trovaId(1));

            annoDidatticoService.rimuoviAnno(annoDidattico);
            verify(annoDidatticoDao).rimuoviAnno(annoDidattico);
        }
    }
}
