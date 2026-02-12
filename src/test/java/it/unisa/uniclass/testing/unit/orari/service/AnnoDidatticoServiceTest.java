package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.service.AnnoDidatticoService;
import it.unisa.uniclass.orari.service.dao.AnnoDidatticoRemote;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.Collections;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class AnnoDidatticoServiceTest {

    @Mock
    private AnnoDidatticoRemote dao;

    @InjectMocks
    private AnnoDidatticoService service;

    @Test
    @DisplayName("Trova per stringa anno")
    void testTrovaAnno() {
        service.trovaAnno("2023/2024");
        verify(dao).trovaAnno("2023/2024");
    }

    @Test
    @DisplayName("Trova per ID: Successo")
    void testTrovaId_Success() {
        AnnoDidattico ad = new AnnoDidattico();
        when(dao.trovaId(1)).thenReturn(ad);
        assertSame(ad, service.trovaId(1));
    }

    @Test
    @DisplayName("Trova per ID: Non Trovato")
    void testTrovaId_NotFound() {
        when(dao.trovaId(99)).thenThrow(new NoResultException());
        assertNull(service.trovaId(99));
    }

    @Test
    @DisplayName("Trova Tutti")
    void testTrovaTutti() {
        when(dao.trovaTutti()).thenReturn(Collections.emptyList());
        assertTrue(service.trovaTutti().isEmpty());
    }

    @Test
    @DisplayName("Aggiungi Anno")
    void testAggiungiAnno() {
        AnnoDidattico ad = new AnnoDidattico();
        service.aggiungiAnno(ad);
        verify(dao).aggiungiAnno(ad);
    }

    @Test
    @DisplayName("Rimuovi Anno")
    void testRimuoviAnno() {
        AnnoDidattico ad = new AnnoDidattico();
        service.rimuoviAnno(ad);
        verify(dao).rimuoviAnno(ad);
    }

    @Test
    @DisplayName("Trova Tutti per Corso Laurea (ID)")
    void testTrovaTuttiCorsoLaurea() {
        service.trovaTuttiCorsoLaurea(5L);
        verify(dao).trovaTuttiCorsoLaurea(5L);
    }

    @Test
    @DisplayName("Trova per Corso Laurea e Nome: Successo")
    void testTrovaCorsoLaureaNome_Success() {
        AnnoDidattico ad = new AnnoDidattico();
        when(dao.trovaCorsoLaureaNome(1L, "2023")).thenReturn(ad);
        assertSame(ad, service.trovaTuttiCorsoLaureaNome(1L, "2023"));
    }

    @Test
    @DisplayName("Trova per Corso Laurea e Nome: Non Trovato")
    void testTrovaCorsoLaureaNome_NotFound() {
        when(dao.trovaCorsoLaureaNome(anyLong(), anyString())).thenThrow(new NoResultException());
        assertNull(service.trovaTuttiCorsoLaureaNome(1L, "2020"));
    }
}