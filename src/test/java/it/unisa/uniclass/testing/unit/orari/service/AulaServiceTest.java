package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.Aula;
import it.unisa.uniclass.orari.service.AulaService;
import it.unisa.uniclass.orari.service.dao.AulaRemote;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class AulaServiceTest {

    @Mock
    private AulaRemote aulaDAO;

    @InjectMocks
    private AulaService service;

    // --- RICERCA SINGOLA (ID e NOME) ---
    @Test
    void testTrovaAulaById_Success() {
        Aula a = new Aula();
        when(aulaDAO.trovaAula(1)).thenReturn(a);
        assertSame(a, service.trovaAula(1));
    }

    @Test
    void testTrovaAulaById_NotFound() {
        when(aulaDAO.trovaAula(1)).thenThrow(new NoResultException());
        assertNull(service.trovaAula(1));
    }

    @Test
    void testTrovaAulaByNome_Success() {
        Aula a = new Aula();
        when(aulaDAO.trovaAula("F1")).thenReturn(a);
        assertSame(a, service.trovaAula("F1"));
    }

    @Test
    void testTrovaAulaByNome_NotFound() {
        when(aulaDAO.trovaAula("X")).thenThrow(new NoResultException());
        assertNull(service.trovaAula("X"));
    }

    // --- RICERCA LISTE ---
    @Test
    void testTrovaTutte() {
        when(aulaDAO.trovaTutte()).thenReturn(Collections.emptyList());
        assertTrue(service.trovaTutte().isEmpty());
        verify(aulaDAO).trovaTutte();
    }

    @Test
    void testTrovaAuleEdificio() {
        service.trovaAuleEdificio("F");
        verify(aulaDAO).trovaAuleEdificio("F");
    }

    @Test
    void testTrovaEdifici() {
        service.trovaEdifici();
        verify(aulaDAO).trovaEdifici();
    }

    // --- AGGIUNGI (Con Null Check) ---
    @Test
    void testAggiungiAula_Success() {
        Aula a = new Aula();
        service.aggiungiAula(a);
        verify(aulaDAO).aggiungiAula(a);
    }

    @Test
    void testAggiungiAula_Null() {
        assertThrows(IllegalArgumentException.class, () -> service.aggiungiAula(null));
        verifyNoInteractions(aulaDAO);
    }

    // --- RIMUOVI (Con Null Check) ---
    @Test
    void testRimuoviAula_Success() {
        Aula a = new Aula();
        service.rimuoviAula(a);
        verify(aulaDAO).rimuoviAula(a);
    }

    @Test
    void testRimuoviAula_Null() {
        assertThrows(IllegalArgumentException.class, () -> service.rimuoviAula(null));
        verifyNoInteractions(aulaDAO);
    }
}